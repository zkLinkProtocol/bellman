use crate::pairing::ff::{Field, PrimeField, PrimeFieldRepr};
use crate::pairing::{Engine, CurveAffine, CurveProjective};
use crate::bit_vec::BitVec;

use crate::{SynthesisError};
use std::marker::PhantomData;
use std::sync::{Mutex, Arc};
use std::ops::{Range, DerefMut};

use crate::plonk::domains::*;
pub use crate::plonk::cs::variable::*;
use crate::plonk::better_cs::utils::*;
pub use super::lookup_tables::{self, *};
use heavy_ops_service::Worker;
use async_utils::SubVec;
use futures::future::join_all;
use async_data_structures::*;
use async_polynomials::*;

use crate::plonk::fft::cooley_tukey_ntt::*;

use super::utils::*;
use super::cs::*;



impl<E: Engine, P: PlonkConstraintSystemParams<E>, MG: MainGate<E>, S: SynthesisMode> Assembly<E, P, MG, S> {
    pub async fn async_calculate_t_polynomial_values_for_single_application_tables(
        &self,
        worker: Worker,
        is_background: bool
    ) -> Result<Vec<Vec<E::Fr>>, SynthesisError> {

        if !S::PRODUCE_SETUP {
            return Err(SynthesisError::AssignmentMissing);
        }
        
        if self.tables.len() == 0 {
            return Ok(vec![])
        }
        
        // we should pass over every table and append it

        let mut width = 0;
        for table in self.tables.iter() {
            if width == 0 {
                width = table.width();
            } else {
                assert_eq!(width, table.width());
            }
        }

        assert_eq!(width, 3, "only support tables that span over 3 polynomials for now");

        let mut column_contributions = vec![Arc::new(Mutex::new(vec![])); width + 1];

        for table in self.tables.iter() {
            // let entries = table.get_table_values_for_polys();
            let entries = Self::ensure_sorted_table(table);
            // these are individual column vectors, so just copy
            let table_id = table.table_id();
            let entries_len = entries[0].len();
            
            let mut handles = vec![];
            for (idx, ent) in entries.into_iter().enumerate() {
                let child_worker = worker.child();
                let column_contributions_idx = column_contributions[idx].clone();

                let fut = async move {
                    
                    let cpu_unit = child_worker.get_cpu_unit(is_background).await.await;

                    {
                        let mut lock = column_contributions_idx.lock().unwrap();
                        lock.extend(ent);
                    }

                    child_worker.return_resources(cpu_unit).await;
                };
                let handle = worker.spawn_with_handle(fut).unwrap();
                handles.push(handle);
            }

            let child_worker = worker.child();
            let column_contributions_idx = column_contributions[3].clone();

            let fut = async move {
                let cpu_unit = child_worker.get_cpu_unit(is_background).await.await;

                {
                    let mut lock = column_contributions_idx.lock().unwrap();
                    let new_length = entries_len + lock.len();
                    lock.resize(new_length, table_id);
                }

                child_worker.return_resources(cpu_unit).await;
            };
            let handle = worker.spawn_with_handle(fut).unwrap();
            handles.push(handle);
        }

        let column_contributions = column_contributions
            .into_iter()
            .map(|sv| 
                Arc::try_unwrap(sv)
                .unwrap()
                .into_inner()
                .unwrap())
            .collect();

        Ok(column_contributions)
    }

    pub async fn async_calculate_s_poly_contributions_from_witness(
        &'static self, 
        worker: Worker, 
        is_background: bool
    ) -> Result<Vec<Vec<E::Fr>>, SynthesisError> 
    {
        if self.tables.len() == 0 {
            return Ok(vec![]);
        }
        let num_cpus = worker.num_cpus();
        // we first form a set of all occured witness values,
        // then include table entries to the set
        // and then sort this set

        let mut contributions_per_column = vec![Arc::new(Mutex::new(vec![]))];
        for single_application in self.tables.iter() {
            let mut kv_set_entries = Arc::new(Mutex::new(vec![]));
            // copy all queries from witness
            let table_name = single_application.functional_name();
            let individual_table_entries = Arc::new(self.individual_table_entries.get(&table_name).unwrap());
            let worker_ranges_1 = ranges_from_length_and_num_cpus(individual_table_entries.len(), num_cpus);

            // copy table elements themselves
            let entries = Arc::new(Self::ensure_sorted_table(single_application));
            let worker_ranges_2 = ranges_from_length_and_num_cpus(entries[0].len(), num_cpus);

            let mut handles = vec![];
            for (range_1, range_2) in worker_ranges_1.into_iter().zip(worker_ranges_2.into_iter()) {
                let child_worker = worker.child();
                let individual_table_entries_clone = individual_table_entries.clone();
                let entries_clone = entries.clone();
                let kv_set_entries_clone = kv_set_entries.clone();

                let fut = async move {
                    let cpu_unit = child_worker.get_cpu_unit(is_background).await.await;

                    for kv_values in individual_table_entries_clone[range_1].iter() {
                        let entry = KeyValueSet::<E>::from_slice(&kv_values[..3]);
                        let mut lock = kv_set_entries_clone.lock().unwrap();
                        lock.push(entry);
                    }

                    for i in range_2 {
                        let entry = KeyValueSet::new([entries_clone[0][i], entries_clone[1][i], entries_clone[2][i]]);
                        let mut lock = kv_set_entries_clone.lock().unwrap();
                        lock.push(entry);
                    }

                    child_worker.return_resources(cpu_unit).await;
                };
                let handle = worker.spawn_with_handle(fut).unwrap();
                handles.push(handle);
            }
            join_all(handles).await;

            let mut kv_set_entries = Arc::try_unwrap(kv_set_entries).unwrap().into_inner().unwrap();
            kv_set_entries.sort();
            let kv_set_entries = Arc::new(kv_set_entries);

            // now copy backward with addition of the table id
            let lock = contributions_per_column[0].lock().unwrap();
            let prev_length = lock.len() + kv_set_entries.len();
            drop(lock);
            let kv_set_entries_len = kv_set_entries.len();
            let table_id = single_application.table_id();

            let mut handles = vec![];
            for i in 0..4 {
                let child_worker = worker.child();
                let contributions_per_column_clone = contributions_per_column[i].clone();
                let kv_set_entries_clone = kv_set_entries.clone();

                if i == 4 {
                    let fut = async move {
                        let cpu_unit = child_worker.get_cpu_unit(is_background).await.await;

                        {
                            let mut lock = contributions_per_column_clone.lock().unwrap();
                            let new_length = lock.len() + kv_set_entries_clone.len();
                            lock.resize(new_length, table_id);
                        }

                        child_worker.return_resources(cpu_unit).await;
                    };

                    let handle = worker.spawn_with_handle(fut).unwrap();
                    handles.push(handle);
                } else {
                    let fut = async move {
                        let cpu_unit = child_worker.get_cpu_unit(is_background).await.await;

                        {
                            let mut lock = contributions_per_column_clone.lock().unwrap();
                            for kv in kv_set_entries_clone.iter() {
                                lock.push(kv.inner[i]);
                            }
                        }

                        child_worker.return_resources(cpu_unit).await;
                    };

                    let handle = worker.spawn_with_handle(fut).unwrap();
                    handles.push(handle);

                }
            }
            join_all(handles).await;
        }

        let contributions_per_column = contributions_per_column
            .into_iter()
            .map(|sv| 
                Arc::try_unwrap(sv)
                .unwrap()
                .into_inner()
                .unwrap())
            .collect();

        Ok(contributions_per_column)
    }


    pub async fn async_calculate_lookup_selector_values(
        &'static self,
        worker: Worker,
        is_background: bool,
    ) -> Result<Vec<E::Fr>, SynthesisError> {
        assert!(self.is_finalized);

        if !S::PRODUCE_SETUP {
            return Err(SynthesisError::AssignmentMissing);
        }

        if self.tables.len() == 0 {
            return Ok(vec![]);
        }

        // total number of gates, Input + Aux
        let size = self.n();
        let num_cpus = worker.num_cpus();

        let aux_gates_start = self.num_input_gates;

        let num_aux_gates = self.num_aux_gates;
        // input + aux gates without t-polys
        let length = self.tables.len();
        let worker_ranges = ranges_from_length_and_num_cpus(length, num_cpus);

        let tables = Arc::new(&self.tables);
        let selectors = Arc::new(&self.table_selectors);
        let mut lookup_selector_values = SubVec::new(vec![E::Fr::zero(); size]);

        let mut handles = vec![];
        for range in worker_ranges.into_iter() {
            let child_worker = worker.child();
            let mut lookup_selector_values_clone = lookup_selector_values.clone();
            let tables_clone = tables.clone();
            let selectors_clone = selectors.clone();

            let fut = async move {
                let cpu_unit = child_worker.get_cpu_unit(is_background).await.await;

                for i in range {
                    let table_name = tables_clone[i].functional_name();
                    let selector_bitvec = selectors_clone.get(&table_name).unwrap();

                    let selector_values = lookup_selector_values_clone.deref_mut();
                    for aux_gate_idx in 0..num_aux_gates {
                        if selector_bitvec[aux_gate_idx] {
                            let global_gate_idx = aux_gate_idx + aux_gates_start;
                            // place 1 into selector
                            selector_values[global_gate_idx] = E::Fr::one();
                        }
                    }
                }

                child_worker.return_resources(cpu_unit).await;
            };
            let handle = worker.spawn_with_handle(fut).unwrap();
            handles.push(handle);
        }
        join_all(handles).await;

        Ok(lookup_selector_values.into_inner())
    }

    pub async fn async_calculate_masked_lookup_entries_using_selector(
        &self,
        storage: &AsyncAssembledPolynomialStorage<E>,
        selector: &Polynomial<E::Fr, Values>,
        worker: Worker,
        is_background: bool,
    ) -> 
        Result<Vec<Vec<E::Fr>>, SynthesisError>
    {
        assert!(self.is_finalized);
        if self.tables.len() == 0 {
            return Ok(vec![]);
        }

        // total number of gates, Input + Aux
        let size = self.n();

        let aux_gates_start = self.num_input_gates;

        let num_aux_gates = self.num_aux_gates;
        // input + aux gates without t-polys

        let selector_ref = selector.as_ref().as_ref();

        let one = E::Fr::one();

        let mut contributions_per_column = vec![vec![E::Fr::zero(); size]; 3];
        for single_application in self.tables.iter() {
            let keys_and_values = single_application.applies_over();

            for aux_gate_idx in 0..num_aux_gates {
                let global_gate_idx = aux_gate_idx + aux_gates_start;

                if selector_ref[global_gate_idx] == one {
                    // place value into f poly
                    for (idx, &poly_id) in keys_and_values.iter().enumerate() {
                        let value = storage.get_poly_at_step(poly_id, global_gate_idx);
                        contributions_per_column[idx][global_gate_idx] = value;
                    }
                }
            }
        }

        Ok(contributions_per_column)
    }
}

fn ranges_from_length_and_num_cpus(length: usize, num_cpus: usize) -> Vec<Range<usize>> {
    assert!(num_cpus > 0);
    let mut result = vec![];

    let mut size = length / num_cpus;
    if length % num_cpus != 0 {
        size += 1;
    }
    let mut current_start = 0;

    while (current_start + size) < length {
        result.push(current_start..(current_start + size));
        current_start += size;
    }
    result.push(current_start..length);

    result
}
