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

    pub(crate) async fn async_ensure_sorted_table(
        table: Arc<LookupTableApplication<E>>, 
        worker: Worker, 
        is_background: bool
    ) -> Vec<Vec<E::Fr>> {
        let entries = Arc::new(table.get_table_values_for_polys());
        assert_eq!(entries.len(), 3);
        let num_cpus = worker.num_cpus();

        // sort them in a standard lexicographic way, so our sorting is always simple
        let size = entries[0].len();
        let mut kv_set_entries = Vec::with_capacity(size);
        unsafe {
            kv_set_entries.set_len(size);
        }
        let mut kv_set_entries = SubVec::new(kv_set_entries);
        let mut kv_set_entries_chunks = kv_set_entries.clone().split_by_num_cpus(num_cpus);
        let mut handles = vec![];

        for mut chunk in kv_set_entries_chunks.into_iter() {
            let worker_child = worker.child();
            let entries_clone = entries.clone();

            let fut = async move {
                let cpu_unit = worker_child.get_cpu_unit(is_background).await.await;

                let range = chunk.range.clone();
                let mut chunk_buf = chunk.deref_mut();
                for (i, el) in range.zip(chunk_buf.iter_mut()) {
                    let entry = KeyValueSet::<E>::new([entries_clone[0][i], entries_clone[1][i], entries_clone[2][i]]);
                    *el = entry;
                }

                worker_child.return_resources(cpu_unit).await;
            };
            let handle = worker.spawn_with_handle(fut).unwrap();
            handles.push(handle);
        }
        join_all(handles).await;

        let mut kv_set_entries = kv_set_entries.into_inner();
        kv_set_entries.sort();
        let kv_set_entries = Arc::new(kv_set_entries);

        let mut result_0 = Vec::with_capacity(size);
        let mut result_1 = Vec::with_capacity(size);
        let mut result_2 = Vec::with_capacity(size);

        unsafe {
            result_0.set_len(size);
            result_1.set_len(size);
            result_2.set_len(size);
        }

        let mut result_0 = SubVec::new(result_0);
        let mut result_1 = SubVec::new(result_1);
        let mut result_2 = SubVec::new(result_2);

        // let mut result_0 = SubVec::new(vec![E::Fr::zero(); size]);
        // let mut result_1 = SubVec::new(vec![E::Fr::zero(); size]);
        // let mut result_2 = SubVec::new(vec![E::Fr::zero(); size]);

        let mut result_0_chunks = result_0.clone().split_by_num_cpus(num_cpus);
        let mut result_1_chunks = result_1.clone().split_by_num_cpus(num_cpus);
        let mut result_2_chunks = result_2.clone().split_by_num_cpus(num_cpus);

        let mut handles = vec![];

        for (mut chunk_0, mut chunk_1, mut chunk_2) in itertools::izip!(
            result_0_chunks.into_iter(),
            result_1_chunks.into_iter(),
            result_2_chunks.into_iter()
        ) {
            let worker_child = worker.child();
            let kv_set_entries_clone = kv_set_entries.clone();

            let fut = async move {
                let cpu_unit = worker_child.get_cpu_unit(is_background).await.await;

                let range = chunk_0.range.clone();
                let chunk_0_buf = chunk_0.deref_mut();
                let chunk_1_buf = chunk_1.deref_mut();
                let chunk_2_buf = chunk_2.deref_mut();

                for (j, i) in range.enumerate() {
                    chunk_0_buf[j] = kv_set_entries_clone[i].inner[0];
                    chunk_1_buf[j] = kv_set_entries_clone[i].inner[1];
                    chunk_2_buf[j] = kv_set_entries_clone[i].inner[2];
                }

                worker_child.return_resources(cpu_unit).await;
            };
            let handle = worker.spawn_with_handle(fut).unwrap();
            handles.push(handle);
        }
        join_all(handles).await;

        vec![result_0.into_inner(), result_1.into_inner(), result_2.into_inner()]
    }

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

        let mut column_contributions: Vec<Arc<Mutex<Vec<E::Fr>>>> = (0..(width+1))
            .into_iter()
            .map(|_| 
                Arc::new(Mutex::new(vec![]))
            ).collect();

        for table in self.tables.iter() {
            // let entries = table.get_table_values_for_polys();
            let entries = Self::async_ensure_sorted_table(table.clone(), worker.child(), is_background).await;
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

            join_all(handles).await;
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
        &self,
        worker: Worker,
        is_background: bool
    ) -> Result<Vec<Vec<E::Fr>>, SynthesisError> {
        if self.tables.len() == 0 {
            return Ok(vec![]);
        }
        let num_cpus = worker.num_cpus();
        // we first form a set of all occured witness values,
        // then include table entries to the set
        // and then sort this set

        let mut contributions_per_column = vec![
            Arc::new(Mutex::new(vec![])),
            Arc::new(Mutex::new(vec![])),
            Arc::new(Mutex::new(vec![])),
            Arc::new(Mutex::new(vec![]))];

        for single_application in self.tables.iter() {
            let mut kv_set_entries = Arc::new(Mutex::new(vec![]));
            // copy all queries from witness
            let table_name = single_application.functional_name();
            let individual_table_entries = self.individual_table_entries.get(&table_name).unwrap().clone();
            let worker_ranges_1 = ranges_from_length_and_num_cpus(individual_table_entries.read().unwrap().len(), num_cpus);

            // copy table elements themselves
            let entries = Self::async_ensure_sorted_table(single_application.clone(), worker.child(), is_background).await;
            let worker_ranges_2 = ranges_from_length_and_num_cpus(entries[0].len(), num_cpus);

            let mut handles = vec![];
            for range_1 in worker_ranges_1.into_iter() {
                let child_worker = worker.child();
                let individual_table_entries_clone = individual_table_entries.clone();
                let kv_set_entries_clone = kv_set_entries.clone();

                let fut = async move {
                    let cpu_unit = child_worker.get_cpu_unit(is_background).await.await;

                    for kv_values in individual_table_entries_clone.read().unwrap()[range_1].iter() {
                        let entry = KeyValueSet::<E>::from_slice(&kv_values[..3]);
                        let mut lock = kv_set_entries_clone.lock().unwrap();
                        lock.push(entry);
                    }

                    child_worker.return_resources(cpu_unit).await;
                };
                let handle = worker.spawn_with_handle(fut).unwrap();
                handles.push(handle);
            }
            join_all(handles).await;

            let mut handles = vec![];
            for range_2 in worker_ranges_2.into_iter() {
                let child_worker = worker.child();
                let entries_clone = entries.clone();
                let kv_set_entries_clone = kv_set_entries.clone();

                let fut = async move {
                    let cpu_unit = child_worker.get_cpu_unit(is_background).await.await;

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

                if i == 3 {
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
        &self,
        worker: Worker,
        is_background: bool
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

        let mut lookup_selector_values = Vec::with_capacity(size);
        unsafe {
            lookup_selector_values.set_len(size);
        }
        let mut lookup_selector_values = SubVec::new(lookup_selector_values);

        let mut first_round = true;

        for single_application in self.tables.iter() {
            let mut handles = vec![];

            for mut chunk in lookup_selector_values.clone().split_by_num_cpus(num_cpus).into_iter(){
                let single_application_clone = single_application.clone();
                let table_selectors = self.table_selectors.clone();
                let worker_child = worker.child();

                let fut = async move {
                    let cpu_unit = worker_child.get_cpu_unit(is_background).await.await;

                    {
                        let table_name = single_application_clone.functional_name();
                        let lock = table_selectors.read().unwrap();
                        let selector_bitvec = lock.get(&table_name).unwrap();

                        let range = chunk.range.clone();
                        let chunk_buf = chunk.deref_mut();

                        for (idx, aux_gate_idx) in range.enumerate() {
                            if selector_bitvec[aux_gate_idx] {
                                // place 1 into selector
                                chunk_buf[idx] = E::Fr::one();
                            } else if first_round {
                                chunk_buf[idx] = E::Fr::zero();
                            }
                        }
                    }

                    worker_child.return_resources(cpu_unit).await;
                };

                let handle = worker.spawn_with_handle(fut).unwrap();
                handles.push(handle);
            }
            join_all(handles).await;

            first_round = false;
        }

        Ok(lookup_selector_values.into_inner())
    }

    pub async fn async_calculate_masked_lookup_entries_using_selector(
        &self,
        storage: Arc<AsyncAssembledPolynomialStorage<E>>,
        selector: Polynomial<E::Fr, Values>,
        worker: Worker,
        is_background: bool,
    ) -> Result<Vec<Vec<E::Fr>>, SynthesisError> {
        assert!(self.is_finalized);
        if self.tables.len() == 0 {
            return Ok(vec![]);
        }

        // total number of gates, Input + Aux
        let size = self.n();
        let num_cpus = worker.num_cpus();

        let aux_gates_start = self.num_input_gates;

        let num_aux_gates = self.num_aux_gates;
        // input + aux gates without t-polys

        let one = E::Fr::one();

        let mut contributions_per_column_0 = Vec::with_capacity(size);
        let mut contributions_per_column_1 = Vec::with_capacity(size);
        let mut contributions_per_column_2 = Vec::with_capacity(size);

        unsafe {
            contributions_per_column_0.set_len(size);
            contributions_per_column_1.set_len(size);
            contributions_per_column_2.set_len(size);
        }

        let mut contributions_per_column_0 = SubVec::new(contributions_per_column_0);
        let mut contributions_per_column_1 = SubVec::new(contributions_per_column_1);
        let mut contributions_per_column_2 = SubVec::new(contributions_per_column_2);
        
        let mut first_round = true;
        for single_application in self.tables.iter() {

            let mut handles = vec![];
            for (mut chunk_0, mut chunk_1, mut chunk_2) in itertools::izip!( 
                contributions_per_column_0.clone().split_by_num_cpus(num_cpus).into_iter(),
                contributions_per_column_1.clone().split_by_num_cpus(num_cpus).into_iter(),
                contributions_per_column_2.clone().split_by_num_cpus(num_cpus).into_iter()
            ) {
                let worker_child = worker.child();
                let storage_clone = storage.clone();
                let selector_clone = selector.clone();
                let single_application_clone = single_application.clone();

                let fut = async move {
                    let cpu_unit = worker_child.get_cpu_unit(is_background).await.await;
                    let keys_and_values = single_application_clone.applies_over();
    
                    let range = chunk_0.range.clone();
                    let chunk_0_buf = chunk_0.deref_mut();
                    let chunk_1_buf = chunk_1.deref_mut();
                    let chunk_2_buf = chunk_2.deref_mut();

                    let selector_ref = selector_clone.as_ref();

                    for (idx_in_chunk, aux_gate_idx) in range.enumerate() {
                        let global_gate_idx = aux_gate_idx + aux_gates_start;
        
                        if selector_ref[global_gate_idx] == one {
                            // place value into f poly
                            let value = storage_clone.get_poly_at_step(keys_and_values[0], global_gate_idx);
                            chunk_0_buf[idx_in_chunk] = value;
                            let value = storage_clone.get_poly_at_step(keys_and_values[1], global_gate_idx);
                            chunk_1_buf[idx_in_chunk] = value;
                            let value = storage_clone.get_poly_at_step(keys_and_values[2], global_gate_idx);
                            chunk_2_buf[idx_in_chunk] = value;
                        } else if first_round {
                            chunk_0_buf[idx_in_chunk] = E::Fr::zero();
                            chunk_1_buf[idx_in_chunk] = E::Fr::zero();
                            chunk_2_buf[idx_in_chunk] = E::Fr::zero();
                        }
                    }
    
                    worker_child.return_resources(cpu_unit).await;
                };
                let handle = worker.spawn_with_handle(fut).unwrap();
                handles.push(handle);
            }
            join_all(handles).await;

            first_round = false;
        }

        Ok(vec![
            contributions_per_column_0.into_inner(),
            contributions_per_column_1.into_inner(),
            contributions_per_column_2.into_inner()
        ])
    }

    pub async fn async_make_assembled_poly_storage(
        &self, 
        worker: Worker, 
        with_finalization: bool
    ) -> Result<AsyncAssembledPolynomialStorage<E>, SynthesisError> {
        if with_finalization {
            assert!(self.is_finalized);
        }
        
        let (state_polys, witness_polys) = self.async_make_state_and_witness_polynomials(worker.child(), with_finalization).await?;

        let worker = worker.next();

        let mut state_polys_map = std::collections::HashMap::new();
        for (idx, poly) in state_polys.into_iter().enumerate() {
            let key = PolyIdentifier::VariablesPolynomial(idx);
            let p = Polynomial::from_values_unpadded(poly)?;
            state_polys_map.insert(key, p);
        }

        let mut witness_polys_map = std::collections::HashMap::new();
        for (idx, poly) in witness_polys.into_iter().enumerate() {
            let key = PolyIdentifier::WitnessPolynomial(idx);
            let p = Polynomial::from_values_unpadded(poly)?;
            witness_polys_map.insert(key, p);
        }

        let mut setup_map = std::collections::HashMap::new();
        let mut gate_selectors_map = std::collections::HashMap::new();

        if S::PRODUCE_SETUP {
            let setup_polys_map = self.make_setup_async_polynomials(with_finalization)?;
            let gate_selectors = self.async_output_gate_selectors(worker.child()).await?;

            for (gate, poly) in self.sorted_gates.iter().zip(gate_selectors.into_iter()) {
                // let key = gate.clone();
                let key = PolyIdentifier::GateSelector(gate.name());
                let p = Polynomial::from_values_unpadded(poly)?;
                gate_selectors_map.insert(key, p);
            }

            for (key, p) in setup_polys_map.into_iter() {
                setup_map.insert(key, p);
            }
        }

        let assembled = AsyncAssembledPolynomialStorage::<E> {
            state_map: state_polys_map,
            witness_map: witness_polys_map,
            setup_map: setup_map,
            scratch_space: std::collections::HashMap::new(),
            gate_selectors: gate_selectors_map,
            named_polys: std::collections::HashMap::new(),
            is_bitreversed: false,
            lde_factor: 1
        };

        Ok(assembled)
    }

    fn make_setup_async_polynomials(
        &self,
        with_finalization: bool
    ) -> Result<std::collections::HashMap<PolyIdentifier, Polynomial<E::Fr, Values>>, SynthesisError> {
        if with_finalization {
            assert!(self.is_finalized);
        }

        if !S::PRODUCE_SETUP {
            return Err(SynthesisError::AssignmentMissing);
        }

        let total_num_gates = self.n();
        let num_input_gates = self.num_input_gates;

        let mut map = std::collections::HashMap::new();

        let setup_poly_ids: Vec<_> = self.aux_storage.setup_map.keys().collect();

        for &id in setup_poly_ids.into_iter() {
            let mut assembled_poly = vec![E::Fr::zero(); total_num_gates];
            if num_input_gates != 0 {
                let input_gates_coeffs = &mut assembled_poly[..num_input_gates];
                input_gates_coeffs.copy_from_slice(&self.inputs_storage.setup_map.get(&id).unwrap()[..]);
            }

            {
                let src = &self.aux_storage.setup_map.get(&id).unwrap()[..];
                let src_len = src.len();
                let aux_gates_coeffs = &mut assembled_poly[num_input_gates..(num_input_gates+src_len)];
                aux_gates_coeffs.copy_from_slice(src);
            }

            let as_poly = Polynomial::from_values_unpadded(assembled_poly)?;

            map.insert(id, as_poly);
        }

        Ok(map)
    }

    // TODO
    pub async fn async_output_gate_selectors(&self, worker: Worker) -> Result<Vec<Vec<E::Fr>>, SynthesisError> {
        if self.sorted_gates.len() == 1 {
            return Ok(vec![]);
        }

        let num_gate_selectors = self.sorted_gates.len();

        let one = E::Fr::one();
        let empty_poly_values = vec![E::Fr::zero(); self.n()];
        let mut poly_values = vec![empty_poly_values.clone(); num_gate_selectors];
        let num_input_gates = self.num_input_gates;

        // first gate in sorted in a main gate and applies on public inputs
        for p in poly_values[0][..num_input_gates].iter_mut() {
            *p = one;
        }

        let old_worker = crate::worker::Worker::new_with_cpus(worker.num_cpus());

        old_worker.scope(poly_values.len(), |scope, chunk| {
            for (i, lh) in poly_values.chunks_mut(chunk)
                            .enumerate() {
                scope.spawn(move |_| {
                    // we take `values_per_leaf` values from each of the polynomial
                    // and push them into the conbinations
                    let base_idx = i*chunk;
                    for (j, lh) in lh.iter_mut().enumerate() {
                        let idx = base_idx + j;
                        let id = &self.sorted_gates[idx];
                        let density = self.aux_gate_density.0.get(id).unwrap();
                        let poly_mut_slice: &mut [E::Fr] = &mut lh[num_input_gates..];
                        for (i, d) in density.iter().enumerate() {
                            if d {
                                poly_mut_slice[i] = one;
                            }
                        }
                    }
                });
            }
        });

        Ok(poly_values)
    }

    // TODO
    pub async fn async_make_state_and_witness_polynomials(
        &self,
        worker: Worker,
        with_finalization: bool
    ) -> Result<(Vec<Vec<E::Fr>>, Vec<Vec<E::Fr>>), SynthesisError> {
        if with_finalization {
            assert!(self.is_finalized);
        }

        if !S::PRODUCE_WITNESS {
            return Err(SynthesisError::AssignmentMissing);
        }

        let mut full_assignments = if with_finalization {
            vec![Vec::with_capacity((self.n()+1).next_power_of_two()); P::STATE_WIDTH]
        } else {
            vec![Vec::with_capacity(self.n()+1); P::STATE_WIDTH]
        };

        let pad_to = if with_finalization {
            (self.n()+1).next_power_of_two()
        } else {
            self.n()+1
        };

        let num_input_gates = self.num_input_gates;
        let num_aux_gates = self.num_aux_gates;

        full_assignments[0].extend_from_slice(&self.input_assingments);
        assert!(full_assignments[0].len() == num_input_gates);
        for i in 1..P::STATE_WIDTH {
            full_assignments[i].resize(num_input_gates, E::Fr::zero());
        }

        let dummy = Self::get_dummy_variable();
        
        let old_worker = crate::worker::Worker::new_with_cpus(worker.num_cpus());

        old_worker.scope(full_assignments.len(), |scope, chunk| {
            for (i, lh) in full_assignments.chunks_mut(chunk)
                            .enumerate() {
                scope.spawn(move |_| {
                    // we take `values_per_leaf` values from each of the polynomial
                    // and push them into the conbinations
                    let base_idx = i*chunk;
                    for (j, lh) in lh.iter_mut().enumerate() {
                        let idx = base_idx + j;
                        let id = PolyIdentifier::VariablesPolynomial(idx);
                        let poly_ref = self.aux_storage.state_map.get(&id).unwrap();
                        for i in 0..num_aux_gates {
                            let var = poly_ref.get(i).unwrap_or(&dummy);
                            let value = self.get_value(*var).unwrap();
                            lh.push(value);
                        }
                    }
                });
            }
        });

        for p in full_assignments.iter_mut() {
            p.resize(pad_to - 1, E::Fr::zero());
        }

        for a in full_assignments.iter() {
            assert_eq!(a.len(), pad_to - 1);
        }

        Ok((full_assignments, vec![]))
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


#[cfg(test)]
mod test {
    use super::*;

    use crate::pairing::Engine;
    use crate::pairing::ff::PrimeField;

    struct TestCircuit4WithLookupsManyGatesSmallTable<E:Engine>{
        _marker: PhantomData<E>
    }

    impl<E: Engine> Circuit<E> for TestCircuit4WithLookupsManyGatesSmallTable<E> {
        type MainGate = Width4MainGateWithDNext;

        fn declare_used_gates() -> Result<Vec<Box<dyn GateInternal<E>>>, SynthesisError> {
            Ok(
                vec![
                    Width4MainGateWithDNext::default().into_internal(),
                ]
            )
        }

        fn synthesize<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<(), SynthesisError> {
            let columns = vec![PolyIdentifier::VariablesPolynomial(0), PolyIdentifier::VariablesPolynomial(1), PolyIdentifier::VariablesPolynomial(2)];
            let range_table = LookupTableApplication::new_range_table_of_width_3(2, columns.clone())?;
            let range_table_name = range_table.functional_name();

            let xor_table = LookupTableApplication::new_xor_table(2, columns.clone())?;
            let xor_table_name = xor_table.functional_name();

            let and_table = LookupTableApplication::new_and_table(2, columns)?;
            let and_table_name = and_table.functional_name();

            cs.add_table(range_table)?;
            cs.add_table(xor_table)?;
            cs.add_table(and_table)?;

            let a = cs.alloc(|| {
                Ok(E::Fr::from_str("10").unwrap())
            })?;

            let b = cs.alloc(|| {
                Ok(E::Fr::from_str("20").unwrap())
            })?;

            let c = cs.alloc(|| {
                Ok(E::Fr::from_str("200").unwrap())
            })?;

            let binary_x_value = E::Fr::from_str("3").unwrap();
            let binary_y_value = E::Fr::from_str("1").unwrap();

            let binary_x = cs.alloc(|| {
                Ok(binary_x_value)
            })?;

            let binary_y = cs.alloc(|| {
                Ok(binary_y_value)
            })?;

            let mut negative_one = E::Fr::one();
            negative_one.negate();

            for _ in 0..((1 << 11) - 100) {
                // c - a*b == 0 

                let mut ab_term = ArithmeticTerm::from_variable(a).mul_by_variable(b);
                ab_term.scale(&negative_one);
                let c_term = ArithmeticTerm::from_variable(c);
                let mut term = MainGateTerm::new();
                term.add_assign(c_term);
                term.add_assign(ab_term);

                cs.allocate_main_gate(term)?;
            }

            let dummy = CS::get_dummy_variable();

            // and table
            {
                let table = cs.get_table(&and_table_name)?;
                let num_keys_and_values = table.width();

                let and_result_value = table.query(&[binary_x_value, binary_y_value])?[0];

                let binary_z = cs.alloc(|| {
                    Ok(and_result_value)
                })?;

                cs.begin_gates_batch_for_step()?;

                let vars = [binary_x, binary_y, binary_z, dummy];
                cs.allocate_variables_without_gate(
                    &vars,
                    &[]
                )?;

                cs.apply_single_lookup_gate(&vars[..num_keys_and_values], table)?;

                cs.end_gates_batch_for_step()?;
            }

            let var_zero = cs.get_explicit_zero()?;

            // range table
            {
                let table = cs.get_table(&range_table_name)?;
                let num_keys_and_values = table.width();

                cs.begin_gates_batch_for_step()?;

                let mut term = MainGateTerm::<E>::new();
                term.add_assign(ArithmeticTerm::from_variable_and_coeff(binary_y, E::Fr::zero()));
                term.add_assign(ArithmeticTerm::from_variable_and_coeff(var_zero, E::Fr::zero()));
                term.add_assign(ArithmeticTerm::from_variable_and_coeff(var_zero, E::Fr::zero()));

                let (vars, coeffs) = CS::MainGate::format_linear_term_with_duplicates(term, dummy)?;

                cs.new_gate_in_batch(
                    &CS::MainGate::default(),
                    &coeffs,
                    &vars,
                    &[]
                )?;

                cs.apply_single_lookup_gate(&vars[..num_keys_and_values], table)?;

                cs.end_gates_batch_for_step()?;
            }

            // xor table
            {
                let table = cs.get_table(&xor_table_name)?;
                let num_keys_and_values = table.width();

                let xor_result_value = table.query(&[binary_x_value, binary_y_value])?[0];

                let binary_z = cs.alloc(|| {
                    Ok(xor_result_value)
                })?;

                cs.begin_gates_batch_for_step()?;

                let vars = [binary_x, binary_y, binary_z, dummy];
                cs.allocate_variables_without_gate(
                    &vars,
                    &[]
                )?;

                cs.apply_single_lookup_gate(&vars[..num_keys_and_values], table)?;

                cs.end_gates_batch_for_step()?;
            }

            Ok(())
        }
    }

    use heavy_ops_service::ResourceManagerProxy;
    use futures::executor::block_on;
    #[test]
    fn test_async_functions() {
        use crate::pairing::bn256::{Bn256, Fr};
        use crate::worker::Worker as OldWorker;

        let mut assembly = TrivialAssembly::<Bn256, PlonkCsWidth4WithNextStepParams, Width4MainGateWithDNext>::new();

        let circuit = TestCircuit4WithLookupsManyGatesSmallTable::<Bn256> {
            _marker: PhantomData
        };

        circuit.synthesize(&mut assembly).expect("must work");

        assert!(assembly.gates.len() == 1);

        // println!("Assembly state polys = {:?}", assembly.storage.state_map);

        // println!("Assembly setup polys = {:?}", assembly.storage.setup_map);    

        println!("Assembly contains {} gates", assembly.n());
        assembly.finalize();
        assert!(assembly.is_satisfied());

        assembly.finalize();

        let manager = ResourceManagerProxy::new(num_cpus::get_physical(), 0, 0);
        let worker = manager.create_worker();

        let result_1 = assembly.calculate_t_polynomial_values_for_single_application_tables().unwrap();
        let result_2 = block_on(
            assembly.async_calculate_t_polynomial_values_for_single_application_tables(worker.child(), false)
        ).unwrap();
        assert_eq!(result_1, result_2);

        let result_1 = assembly.calculate_s_poly_contributions_from_witness().unwrap();
        let result_2 = block_on(
            assembly.async_calculate_s_poly_contributions_from_witness(worker.child(), false)
        ).unwrap();
        assert_eq!(result_1, result_2);

        let result_1 = assembly.calculate_lookup_selector_values().unwrap();
        let result_2 = block_on(
            assembly.async_calculate_lookup_selector_values(worker.child(), false)
        ).unwrap();
        assert_eq!(result_1, result_2);

        let old_worker = crate::worker::Worker::new_with_cpus(4);

        let values_storage = assembly.make_assembled_poly_storage(&old_worker, true).unwrap();
        let selector = PolynomialProxy::from_owned(crate::plonk::polynomials::Polynomial::from_values(result_1).unwrap());

        let result_1 = assembly.calculate_masked_lookup_entries_using_selector(&values_storage, &selector).unwrap();

        let values_storage = Arc::new(
            block_on(
                assembly.async_make_assembled_poly_storage(worker.child(), true)
            ).unwrap()
        );
        let selector = Polynomial::from_values(result_2).unwrap();

        let result_2 = block_on(
            assembly.async_calculate_masked_lookup_entries_using_selector(values_storage, selector, worker.child(), false)
        ).unwrap();
        assert_eq!(result_1, result_2);
    }
}