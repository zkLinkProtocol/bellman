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

    pub(crate) async fn async_ensure_sorted_table(table: Arc<LookupTableApplication<E>>, worker: Worker, is_background: bool) -> Vec<Vec<E::Fr>> {
        let entries = Arc::new(table.get_table_values_for_polys());
        assert_eq!(entries.len(), 3);
        let num_cpus = worker.num_cpus();

        // sort them in a standard lexicographic way, so our sorting is always simple
        let size = entries[0].len();
        let mut kv_set_entries = SubVec::new(Vec::with_capacity(size));
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

        let result_0 = SubVec::new(Vec::with_capacity(size));
        let result_1 = SubVec::new(Vec::with_capacity(size));
        let result_2 = SubVec::new(Vec::with_capacity(size));

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

        let mut column_contributions = vec![Arc::new(Mutex::new(vec![])); width + 1];

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

        let mut contributions_per_column = vec![Arc::new(Mutex::new(vec![]))];
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
            for (range_1, range_2) in worker_ranges_1.into_iter().zip(worker_ranges_2.into_iter()) {
                let child_worker = worker.child();
                let individual_table_entries_clone = individual_table_entries.clone();
                let entries_clone = entries.clone();
                let kv_set_entries_clone = kv_set_entries.clone();

                let fut = async move {
                    let cpu_unit = child_worker.get_cpu_unit(is_background).await.await;

                    for kv_values in individual_table_entries_clone.read().unwrap()[range_1].iter() {
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

        let mut lookup_selector_values = SubVec::new(Vec::with_capacity(size));

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
                            }
                        }
                    }

                    worker_child.return_resources(cpu_unit).await;
                };

                let handle = worker.spawn_with_handle(fut).unwrap();
                handles.push(handle);
            }
            join_all(handles).await;
        }

        Ok(lookup_selector_values.into_inner())
    }

    pub async fn async_calculate_masked_lookup_entries_using_selector(
        &self,
        storage: Arc<AsyncAssembledPolynomialStorage<E>>,
        selector: Arc<Polynomial<E::Fr, Values>>,
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
        let num_cpus = worker.num_cpus();

        let aux_gates_start = self.num_input_gates;

        let num_aux_gates = self.num_aux_gates;
        // input + aux gates without t-polys

        let one = E::Fr::one();

        let mut contributions_per_column_0 = SubVec::new(Vec::with_capacity(size));
        let mut contributions_per_column_1 = SubVec::new(Vec::with_capacity(size));
        let mut contributions_per_column_2 = SubVec::new(Vec::with_capacity(size));
        
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

                    let selector_ref = selector_clone.as_ref().as_ref();

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
                        }
                    }
    
                    worker_child.return_resources(cpu_unit).await;
                };
                let handle = worker.spawn_with_handle(fut).unwrap();
                handles.push(handle);
            }
            join_all(handles).await;
        }

        Ok(vec![
            contributions_per_column_0.into_inner(),
            contributions_per_column_1.into_inner(),
            contributions_per_column_2.into_inner()
        ])
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

    struct TestCircuit4<E:Engine>{
        _marker: PhantomData<E>
    }

    impl<E: Engine> Circuit<E> for TestCircuit4<E> {
        type MainGate = Width4MainGateWithDNext;

        fn synthesize<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<(), SynthesisError> {
            let a = cs.alloc(|| {
                Ok(E::Fr::from_str("10").unwrap())
            })?;

            println!("A = {:?}", a);

            let b = cs.alloc(|| {
                Ok(E::Fr::from_str("20").unwrap())
            })?;

            println!("B = {:?}", b);

            let c = cs.alloc(|| {
                Ok(E::Fr::from_str("200").unwrap())
            })?;

            println!("C = {:?}", c);

            let d = cs.alloc(|| {
                Ok(E::Fr::from_str("100").unwrap())
            })?;

            println!("D = {:?}", d);

            let one = E::Fr::one();

            let mut two = one;
            two.double();

            let mut negative_one = one;
            negative_one.negate();

            // 2a - b = 0

            let two_a = ArithmeticTerm::from_variable_and_coeff(a, two);
            let minus_b = ArithmeticTerm::from_variable_and_coeff(b, negative_one);
            let mut term = MainGateTerm::new();
            term.add_assign(two_a);
            term.add_assign(minus_b);

            cs.allocate_main_gate(term)?;

            // c - a*b == 0 

            let mut ab_term = ArithmeticTerm::from_variable(a).mul_by_variable(b);
            ab_term.scale(&negative_one);
            let c_term = ArithmeticTerm::from_variable(c);
            let mut term = MainGateTerm::new();
            term.add_assign(c_term);
            term.add_assign(ab_term);

            cs.allocate_main_gate(term)?;

            // d - 100 == 0 

            let hundred = ArithmeticTerm::constant(E::Fr::from_str("100").unwrap());
            let d_term = ArithmeticTerm::from_variable(d);
            let mut term = MainGateTerm::new();
            term.add_assign(d_term);
            term.sub_assign(hundred);

            cs.allocate_main_gate(term)?;

            // let gamma = cs.alloc_input(|| {
            //     Ok(E::Fr::from_str("20").unwrap())
            // })?;

            let gamma = cs.alloc(|| {
                Ok(E::Fr::from_str("20").unwrap())
            })?;

            // gamma - b == 0 

            let gamma_term = ArithmeticTerm::from_variable(gamma);
            let b_term = ArithmeticTerm::from_variable(b);
            let mut term = MainGateTerm::new();
            term.add_assign(gamma_term);
            term.sub_assign(b_term);

            cs.allocate_main_gate(term)?;

            // 2a
            let mut term = MainGateTerm::<E>::new();
            term.add_assign(ArithmeticTerm::from_variable_and_coeff(a, two));

            let dummy = CS::get_dummy_variable();

            // 2a - d_next = 0

            let (vars, mut coeffs) = CS::MainGate::format_term(term, dummy)?;
            *coeffs.last_mut().unwrap() = negative_one;

            // here d is equal = 2a, so we need to place b there
            // and compensate it with -b somewhere before

            cs.new_single_gate_for_trace_step(&CS::MainGate::default(), 
                &coeffs, 
                &vars, 
                &[]
            )?;

            let mut term = MainGateTerm::<E>::new();
            term.add_assign(ArithmeticTerm::from_variable(b));

            // b + 0 + 0 - b = 0
            let (mut vars, mut coeffs) = CS::MainGate::format_term(term, dummy)?;
            coeffs[3] = negative_one;
            vars[3] = b;

            cs.new_single_gate_for_trace_step(&CS::MainGate::default(), 
                &coeffs, 
                &vars, 
                &[]
            )?;

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

        let circuit = TestCircuit4::<Bn256> {
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

        // let result_1 = assembly.calculate_masked_lookup_entries_using_selector().unwrap();
        // let result_2 = block_on(
        //     assembly.async_calculate_masked_lookup_entries_using_selector(worker.child(), false)
        // ).unwrap();
        // assert_eq!(result_1, result_2);
    }
}