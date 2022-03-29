use crate::SynthesisError;
use crate::plonk::domains::*;
use crate::plonk::fft::cooley_tukey_ntt::bitreverse;
use futures::future::join_all;
use pairing::ff::PrimeField;
use heavy_ops_service::*;
use std::sync::Arc;
use crate::multicore::Worker as OldWorker;
pub trait PolynomialForm: Sized + Copy + Clone {}
use async_utils::SubVec;
use std::ops::{Deref, DerefMut};

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum Coefficients {}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum Values {}

impl PolynomialForm for Coefficients {}
impl PolynomialForm for Values {}

#[derive(PartialEq, Eq, Debug)]
pub struct Polynomial<F: PrimeField, P: PolynomialForm> {
    coeffs: SubVec<F>,
    pub exp: u32,
    pub omega: F,
    pub omegainv: F,
    pub geninv: F,
    pub minv: F,
    _marker: std::marker::PhantomData<P>,
}

impl<F: PrimeField, P: PolynomialForm> Default for Polynomial<F, P> {
    fn default() -> Self {
        Self {
            coeffs: SubVec::<F>::empty(),
            exp: Default::default(),
            omega: Default::default(),
            omegainv: Default::default(),
            geninv: Default::default(),
            minv: Default::default(),
            _marker: Default::default(),
        }
    }
}
impl<F: PrimeField, P: PolynomialForm> Clone for Polynomial<F, P> {
    fn clone(&self) -> Self {
        Self {
            coeffs: self.coeffs.create_copy(),
            exp: self.exp.clone(),
            omega: self.omega.clone(),
            omegainv: self.omegainv.clone(),
            geninv: self.geninv.clone(),
            minv: self.minv.clone(),
            _marker: self._marker.clone(),
        }
    }
}

impl<F: PrimeField, P: PolynomialForm> Polynomial<F, P> {
    pub fn size(&self) -> usize {
        self.coeffs.len()
    }

    pub fn as_ref(&self) -> &[F] {
        self.coeffs.deref()
    }

    pub fn as_mut(&mut self) -> &mut [F] {
        self.coeffs.deref_mut()
    }

    pub fn into_coeffs(self) -> Vec<F> {
        self.coeffs.buf[self.coeffs.range].to_vec()
    }

    pub fn arc_coeffs(&self) -> Arc<Vec<F>> {        
        Arc::clone(&self.coeffs.buf)
    }
    
    pub fn arc_clone(&self) -> Self {        
        Self {
            coeffs: self.coeffs.clone(),
            exp: self.exp.clone(),
            omega: self.omega.clone(),
            omegainv: self.omegainv.clone(),
            geninv: self.geninv.clone(),
            minv: self.minv.clone(),
            _marker: self._marker.clone(),
        }
    }

    pub async fn distribute_powers(&mut self, worker: Worker, is_background: bool, g: F) {
        let num_cpus = worker.num_cpus();
        let mut coeffs_chunks = self.coeffs.clone().split_by_num_cpus(num_cpus);
        let chunk_size = coeffs_chunks[0].len();
        let mut handles = vec![];
        for (chunk_id, (child_worker, mut chunk)) in coeffs_chunks
            .into_iter()
            .map(|chunk| (worker.child(), chunk))
            .enumerate()
        {
            let fut = async move {
                let cpu_unit = child_worker.get_cpu_unit(is_background).await.await;
                let buf = chunk.deref_mut();
                let mut x = g.pow([(chunk_id * chunk_size) as u64]);
                for el in buf.iter_mut() {
                    el.mul_assign(&x);
                    x.mul_assign(&g)
                }
                child_worker.return_resources(cpu_unit).await;
            };
            let handle = worker.spawn_with_handle(fut).unwrap();
            handles.push(handle);
        }
        join_all(handles).await;
    }

    pub fn reuse_allocation<PP: PolynomialForm>(&mut self, other: &Polynomial<F, PP>) {
        assert_eq!(self.coeffs.len(), other.coeffs.len());
        let coeffs = self.coeffs.deref_mut();
        coeffs.copy_from_slice(other.coeffs.deref());
    }

    pub async fn bitreverse_enumeration(&mut self, worker: Worker, is_background: bool) {
        let coeffs = self.coeffs.deref_mut();
        let total_len = coeffs.len();
        let log_n = self.exp as usize;
        if total_len <= worker.num_cpus() {
            for j in 0..total_len {
                let rj = bitreverse(j, log_n);
                if j < rj {
                    coeffs.swap(j, rj);
                }
            }
            return;
        }

        let num_cpus = worker.num_cpus();
        let mut coeffs_chunks = self.coeffs.clone().split_by_num_cpus(num_cpus);
        let mut handles = vec![];

        for (chunk_id, (child_worker, mut coeffs, mut chunk)) in coeffs_chunks
            .into_iter()
            .map(|chunk| (worker.child(), self.coeffs.clone(), chunk))
            .enumerate()
        {
            let fut = async move {
                let cpu_unit = child_worker.get_cpu_unit(is_background).await.await;
                let range = chunk.range.clone();
                let buf = coeffs.deref_mut();

                for j in range {
                    let rj = bitreverse(j, log_n);
                    if j < rj {
                        buf.swap(j, rj);
                    }
                }
                child_worker.return_resources(cpu_unit).await;
            };
            let handle = worker.spawn_with_handle(fut).unwrap();
            handles.push(handle);
        }
        join_all(handles).await;
    }

    pub async fn scale(&mut self, worker: Worker, is_background: bool, g: F) {
        if g == F::one() {
            return;
        }
        op(
            worker,
            is_background,
            Operation::Scale(g),
            self.coeffs.clone(),
        )
        .await;
    }

    pub async fn negate(&mut self, worker: Worker, is_background: bool) {
        op(
            worker,
            is_background,
            Operation::Negate,
            self.coeffs.clone(),
        )
        .await;
    }

    pub fn map<M: Fn(&mut F) -> () + Send + Copy>(&mut self, worker: &OldWorker, func: M)
    {
        todo!();
        // worker.scope(self.coeffs.len(), |scope, chunk| {
        //     for v in self.coeffs.chunks_mut(chunk) {
        //         scope.spawn(move |_| {
        //             for v in v.iter_mut() {
        //                 func(v);
        //             }
        //         });
        //     }
        // });
    }

    pub fn map_indexed<M: Fn(usize, &mut F) -> () + Send + Copy>(&mut self, worker: &OldWorker, func: M)
    {
        // worker.scope(self.coeffs.len(), |scope, chunk| {
        //     for (chunk_idx, v) in self.coeffs.chunks_mut(chunk).enumerate() {
        //         scope.spawn(move |_| {
        //             let base = chunk_idx * chunk;
        //             for (in_chunk_idx, v) in v.iter_mut().enumerate() {
        //                 func(base + in_chunk_idx, v);
        //             }
        //         });
        //     }
        // });

        todo!();
    }

    pub fn pad_by_factor(&mut self, factor: usize) -> Result<(), SynthesisError> {
        let length = self.coeffs.len();
        debug_assert!(length.is_power_of_two());

        if factor == 1 {
            return Ok(());
        }
        
        self.pad_to_size(length * factor);

        Ok(())
    }

    pub fn pad_to_size(&mut self, new_size: usize) -> Result<(), SynthesisError> {
        if new_size < self.coeffs.len() {
            return Err(SynthesisError::PolynomialDegreeTooLarge);
        }
        let next_power_of_two = new_size.next_power_of_two();
        if new_size != next_power_of_two {
            return Err(SynthesisError::Unsatisfiable);
        }

        let mut coeffs = self.coeffs.deref().to_vec();
        coeffs.resize(new_size, F::zero());
        let domain = Domain::new_for_size(new_size as u64)?;
        let m = domain.size as usize;

        *self = Self {
            coeffs: SubVec::new(coeffs),
            exp: domain.power_of_two as u32,
            omega: domain.generator,
            omegainv: self.omega.inverse().unwrap(),
            geninv: self.geninv.clone(),
            minv: F::from_str(&format!("{}", m)).unwrap().inverse().unwrap(),
            _marker: self._marker.clone(),
        };

        Ok(())
    }

    pub fn pad_to_domain(&mut self) -> Result<(), SynthesisError> {
        let domain = Domain::<F>::new_for_size(self.coeffs.len() as u64)?;
        let new_size = domain.size as usize;

        self.pad_to_size(new_size);

        Ok(())
    }

    pub fn clone_padded_to_domain(&self) -> Result<Self, SynthesisError> {
        let mut padded = self.clone();

        padded.pad_to_domain()?;

        Ok(padded)
    }

    pub fn trim_to_degree(&mut self, degree: usize) -> Result<(), SynthesisError> {
        let size = self.coeffs.len();
        if size <= degree + 1 {
            return Ok(());
        }

        let (_, mut coeffs) = self.coeffs.clone().split_at(degree);

        for x in coeffs.deref_mut().iter_mut() {
            *x = F::zero();
        }

        Ok(())
    }
}

impl<F: PrimeField> Polynomial<F, Coefficients> {
    pub fn new_for_size(size: usize) -> Result<Polynomial<F, Coefficients>, SynthesisError> {
        let coeffs = vec![F::zero(); size];

        Self::from_coeffs(coeffs)
    }

    pub fn from_coeffs(coeffs: Vec<F>) -> Result<Polynomial<F, Coefficients>, SynthesisError> {
        let coeffs_len = coeffs.len();
        let mut coeffs = coeffs;

        let domain = Domain::new_for_size(coeffs_len as u64)?;
        let exp = domain.power_of_two as u32;
        let m = domain.size as usize;
        let omega = domain.generator;

        coeffs.resize(m, F::zero());

        Ok(Polynomial::<F, Coefficients> {
            coeffs: SubVec::new(coeffs),
            exp: exp,
            omega: omega,
            omegainv: omega.inverse().unwrap(),
            geninv: F::multiplicative_generator().inverse().unwrap(),
            minv: F::from_str(&format!("{}", m)).unwrap().inverse().unwrap(),
            _marker: std::marker::PhantomData,
        })
    }

    #[inline(always)]
    pub fn break_into_multiples(
        self,
        size: usize,
    ) -> Result<Vec<Polynomial<F, Coefficients>>, SynthesisError> {
        // TODO

        let splited_coeffs = self.coeffs.split_by_chunk_size(size);

        let mut results = Vec::with_capacity(splited_coeffs.len());

        for c in splited_coeffs.iter() {
            let poly = Polynomial::<F, Coefficients>::from_coeffs(c.deref().to_vec())?;
            results.push(poly);
        }

        Ok(results)
    }

    pub fn coset_fft_for_generator(mut self, worker: Worker, gen: F) -> Polynomial<F, Values> {
        todo!()
        // debug_assert!(self.coeffs.len().is_power_of_two());
        // self.distribute_powers(worker, gen);
        // self.fft(worker)
    }

    pub async fn add_assign(
        &self, // FIXME
        worker: Worker,
        is_background: bool,
        other: &Polynomial<F, Coefficients>,
    ) {
        assert!(self.coeffs.len() >= other.coeffs.len());

        bin_op_scaled(
            worker,
            is_background,
            BinOperation::AddAssign,
            self.coeffs.clone(),
            other.coeffs.clone(),
        )
        .await;
    }

    pub async fn add_assign_scaled(
        &mut self,
        worker: Worker,
        is_background: bool,
        other: &Polynomial<F, Coefficients>,
        scaling: &F,
    ) {
        assert!(self.coeffs.len() >= other.coeffs.len());

        bin_op_scaled(
            worker,
            is_background,
            BinOperation::AddAssignScaled(scaling.clone()),
            self.coeffs.clone(),
            other.coeffs.clone(),
        )
        .await;
    }

    /// Perform O(n) subtraction of one polynomial from another in the domain.
    pub async fn sub_assign(
        &mut self,
        worker: Worker,
        is_background: bool,
        other: &Polynomial<F, Coefficients>,
    ) {
        assert!(self.coeffs.len() >= other.coeffs.len());

        bin_op_scaled(
            worker,
            is_background,
            BinOperation::SubAssign,
            self.coeffs.clone(),
            other.coeffs.clone(),
        )
        .await;
    }
    pub async fn sub_assign_scaled(
        &mut self,
        worker: Worker,
        is_background: bool,
        other: &Polynomial<F, Coefficients>,
        scaling: &F,
    ) {
        assert!(self.coeffs.len() >= other.coeffs.len());

        bin_op_scaled(
            worker,
            is_background,
            BinOperation::SubAssignScaled(scaling.clone()),
            self.coeffs.clone(),
            other.coeffs.clone(),
        )
        .await;
    }

    pub async fn evaluate_at(&self, worker: Worker, is_background: bool, g: F) -> F {
        let num_cpus = worker.num_cpus();
        
        let coeffs_chunks = self.coeffs.clone().split_by_num_cpus(num_cpus);
        let chunk_size = coeffs_chunks[0].len();

        let mut handles = vec![];
        for (chunk_id, (child_worker, chunk)) in coeffs_chunks
            .into_iter()
            .map(|chunk| (worker.child(), chunk))
            .enumerate()
        {
            let fut = async move {
                let cpu_unit = child_worker.get_cpu_unit(is_background).await.await;
                let buf = chunk.deref();

                let mut x = g.pow([(chunk_id * chunk_size) as u64]);
                let mut chunk_sum = F::zero();
                for el in buf.iter() {
                    let mut tmp = x;
                    tmp.mul_assign(el);
                    chunk_sum.add_assign(&tmp);
                    x.mul_assign(&g);
                }
                child_worker.return_resources(cpu_unit).await;

                chunk_sum
            };
            let handle = worker.spawn_with_handle(fut).unwrap();
            handles.push(handle);
        }
        let chunk_sums = join_all(handles).await;

        let mut final_sum = F::zero();
        for el in chunk_sums {
            final_sum.add_assign(&el);
        }

        final_sum
    }
}

impl<F: PrimeField> Polynomial<F, Values> {
    pub fn new_for_size(size: usize) -> Result<Polynomial<F, Values>, SynthesisError> {
        let coeffs = vec![F::zero(); size];

        Self::from_values(coeffs)
    }

    pub fn from_values(values: Vec<F>) -> Result<Polynomial<F, Values>, SynthesisError> {
        let coeffs_len = values.len();
        let mut values = values;

        let domain = Domain::new_for_size(coeffs_len as u64)?;
        let exp = domain.power_of_two as u32;
        let m = domain.size as usize;
        let omega = domain.generator;

        values.resize(m, F::zero());

        Ok(Polynomial::<F, Values> {
            coeffs: SubVec::new(values),
            exp: exp,
            omega: omega,
            omegainv: omega.inverse().unwrap(),
            geninv: F::multiplicative_generator().inverse().unwrap(),
            minv: F::from_str(&format!("{}", m)).unwrap().inverse().unwrap(),
            _marker: std::marker::PhantomData,
        })
    }

    pub fn from_values_unpadded(values: Vec<F>) -> Result<Polynomial<F, Values>, SynthesisError> {
        Self::from_arc_values_unpadded(Arc::new(values))
    }
    
    pub fn from_arc_values_unpadded(values: Arc<Vec<F>>) -> Result<Polynomial<F, Values>, SynthesisError> {
        let coeffs_len = values.len();

        let domain = Domain::new_for_size(coeffs_len as u64)?;
        let exp = domain.power_of_two as u32;
        let m = domain.size as usize;
        let omega = domain.generator;

        Ok(Polynomial::<F, Values> {
            coeffs: SubVec::from(values),
            exp: exp,
            omega: omega,
            omegainv: omega.inverse().unwrap(),
            geninv: F::multiplicative_generator().inverse().unwrap(),
            minv: F::from_str(&format!("{}", m)).unwrap().inverse().unwrap(),
            _marker: std::marker::PhantomData,
        })
    }

    // this function should only be used on the values that are bitreverse enumerated
    pub fn clone_subset_assuming_bitreversed(
        &self,
        subset_factor: usize,
    ) -> Result<Polynomial<F, Values>, SynthesisError> {
        if subset_factor == 1 {
            return Ok(self.clone());
        }

        assert!(subset_factor.is_power_of_two());

        let current_size = self.coeffs.len();
        let new_size = current_size / subset_factor;

        let mut result = Vec::with_capacity(new_size);
        unsafe { result.set_len(new_size) };

        // copy elements. If factor is 2 then non-reversed we would output only elements that are == 0 mod 2
        // If factor is 2 and we are bit-reversed - we need to only output first half of the coefficients
        // If factor is 4 then we need to output only the first 4th part
        // if factor is 8 - only the first 8th part

        let start = 0;
        let end = new_size;

        result.copy_from_slice(&self.coeffs.deref()[start..end]);

        Polynomial::from_values(result)
    }

    pub async fn pow(&mut self, worker: Worker, is_background: bool, exp: u64) {
        if exp == 2 {
            return self.square(worker, is_background).await;
        }

        op(
            worker,
            is_background,
            Operation::Pow(exp),
            self.coeffs.clone(),
        )
        .await;
    }

    pub async fn square(&mut self, worker: Worker, is_background: bool) {
        op(
            worker,
            is_background,
            Operation::Square,
            self.coeffs.clone(),
        )
        .await;
    }

    pub async fn add_assign(
        &self,// FIXME &mut self
        worker: Worker,
        is_background: bool,
        other: &Polynomial<F, Values>,
    ) {
        assert_eq!(self.coeffs.len(), other.coeffs.len());

        bin_op_scaled(
            worker,
            is_background,
            BinOperation::AddAssign,
            self.coeffs.clone(),
            other.coeffs.clone(),
        )
        .await;
    }

    // FIXME &mut self
    pub async fn add_constant(&self, worker: Worker, is_background: bool, constant: &F) {
        op(
            worker,
            is_background,
            Operation::Add(constant.clone()),
            self.coeffs.clone(),
        )
        .await;
    }

    pub async fn sub_constant(&mut self, worker: Worker, is_background: bool, constant: &F) {
        op(
            worker,
            is_background,
            Operation::Sub(constant.clone()),
            self.coeffs.clone(),
        )
        .await;
    }

    pub fn rotate(mut self, by: usize) -> Result<Polynomial<F, Values>, SynthesisError> {
        todo!();
        // let mut values: Vec<_> = self.coeffs.drain(by..).collect();

        // for c in self.coeffs.into_iter() {
        //     values.push(c);
        // }

        // Polynomial::from_values(values)
    }

    pub async fn calculate_shifted_grand_product(
        &self,
        worker: Worker,
        is_background: bool,
    ) -> Result<Polynomial<F, Values>, SynthesisError> {
        let num_items = self.coeffs.len();
        let mut result = vec![F::zero(); num_items + 1];
        result[0] = F::one();
        let result = SubVec::new(result);
        let (_, result_part) = result.clone().split_at(1);
        
        calculate_grand_product(worker, is_background, self.coeffs.clone(), result_part).await;
        
        Polynomial::from_values(result.into_inner())
    }

    pub async fn calculate_grand_product(
        &self,
        worker: Worker,
        is_background: bool,
    ) -> Result<Polynomial<F, Values>, SynthesisError> {
        let result = SubVec::new(vec![F::zero(); self.coeffs.len()]);

        calculate_grand_product(worker, is_background, self.coeffs.clone(), result.clone()).await;

        Polynomial::from_values(result.into_inner())
    }

    pub async fn add_assign_scaled(
        &self, // FIXME &mut self
        worker: Worker,
        is_background: bool,
        other: &Polynomial<F, Values>,
        scaling: &F,
    ) {
        assert_eq!(self.coeffs.len(), other.coeffs.len());

        bin_op_scaled(
            worker,
            is_background,
            BinOperation::AddAssignScaled(scaling.clone()),
            self.coeffs.clone(),
            other.coeffs.clone(),
        )
        .await;
    }

    /// Perform O(n) subtraction of one polynomial from another in the domain.
    pub async fn sub_assign(
        &mut self,
        worker: Worker,
        is_background: bool,
        other: &Polynomial<F, Values>,
    ) {
        assert_eq!(self.coeffs.len(), other.coeffs.len());

        bin_op_scaled(
            worker,
            is_background,
            BinOperation::SubAssign,
            self.coeffs.clone(),
            other.coeffs.clone(),
        )
        .await;
    }

    pub async fn sub_assign_scaled(
        &mut self,
        worker: Worker,
        is_background: bool,
        other: &Polynomial<F, Values>,
        scaling: &F,
    ) {
        assert_eq!(self.coeffs.len(), other.coeffs.len());

        bin_op_scaled(
            worker,
            is_background,
            BinOperation::SubAssignScaled(scaling.clone()),
            self.coeffs.clone(),
            other.coeffs.clone(),
        )
        .await;
    }

    /// Perform O(n) multiplication of two polynomials in the domain.
    pub async fn mul_assign(
        &self, // FIXME &mut self
        worker: Worker,
        is_background: bool,
        other: &Polynomial<F, Values>,
    ) {
        assert_eq!(self.coeffs.len(), other.coeffs.len());

        bin_op_scaled(
            worker,
            is_background,
            BinOperation::MulAssign,
            self.coeffs.clone(),
            other.coeffs.clone(),
        )
        .await;
    }

    pub async fn batch_inversion(
        &mut self,
        worker: Worker,
        is_background: bool,
    ) -> Result<(), SynthesisError> {
        let num_cpus = worker.num_cpus();
        let num_items = self.coeffs.len();
        dbg!(num_items);
        let mut grand_products = SubVec::new(vec![F::one(); num_items]);
        let mut sub_products = SubVec::new(vec![F::one(); num_cpus]);

        let mut grand_products_chunks = grand_products.clone().split_by_num_cpus(num_cpus);
        let coeffs_chunks = self.coeffs.clone().split_by_num_cpus(num_cpus);
        let mut chunk_size = coeffs_chunks[0].len();

        let mut handles = vec![];

        for (chunk_id, (child_worker, mut coeffs_chunk, mut grand_products_chunk, mut sub_product)) in itertools::izip!(
            coeffs_chunks.into_iter(),
            grand_products_chunks.into_iter(),)
            .map(|(coeffs_chunk, grand_products_chunk)| {
                (
                    worker.child(),
                    coeffs_chunk,
                    grand_products_chunk,
                    sub_products.clone()
                )
            })
            .enumerate()
        {
            assert!(chunk_id < num_cpus);

            let fut = async move {
                let cpu_unit = child_worker.get_cpu_unit(is_background).await.await;
                let coeffs = coeffs_chunk.deref_mut();
                let grand_products = grand_products_chunk.deref_mut();
                let sub_products = sub_product.deref_mut();

                for (a, g) in coeffs.iter().zip(grand_products.iter_mut()) {
                    sub_products[chunk_id].mul_assign(&a);
                    *g = sub_products[chunk_id];
                }
                child_worker.return_resources(cpu_unit).await;
            };
            let handle = worker.spawn_with_handle(fut).unwrap();
            handles.push(handle);
        }
        join_all(handles).await;

        // now coeffs are [a, b, c, d, ..., z]
        // grand_products are [a, ab, abc, d, de, def, ...., xyz]
        // subproducts are [abc, def, xyz]
        // not guaranteed to have equal length

        let mut full_grand_product = F::one();
        for sub in sub_products.deref().iter() {
            full_grand_product.mul_assign(sub);
        }

        let product_inverse = full_grand_product
            .inverse()
            .ok_or(SynthesisError::DivisionByZero)?;

        // now let's get [abc^-1, def^-1, ..., xyz^-1];

        let mut sub_inverses = vec![F::one(); num_cpus];
        for (i, s) in sub_inverses.iter_mut().enumerate() {
            let mut tmp = product_inverse;
            for (j, p) in sub_products.deref().iter().enumerate() {
                if i == j {
                    continue;
                }
                tmp.mul_assign(&p);
            }

            *s = tmp;
        }

        let mut sub_inverses = SubVec::new(sub_inverses);
        let mut grand_products_chunks = grand_products.split_by_num_cpus(num_cpus);

        let coeffs_chunks = self.coeffs.clone().split_by_num_cpus(num_cpus);
        let mut handles = vec![];
        for (chunk_id, (child_worker, mut coeffs_chunk, mut grand_products_chunk, mut sub_inverses)) in itertools::izip!(
            coeffs_chunks.into_iter(),
            grand_products_chunks.into_iter())
            .map(|(coeffs_chunk, grand_products_chunk)| {
                (
                    worker.child(),
                    coeffs_chunk,
                    grand_products_chunk,
                    sub_inverses.clone()
                )
            })
            .enumerate()
        {
            let fut = async move {
                let cpu_unit = child_worker.get_cpu_unit(is_background).await.await;
                let coeffs = coeffs_chunk.deref_mut();
                let grand_products = grand_products_chunk.deref_mut();
                let sub_inverses = sub_inverses.deref_mut();

                for (a, g) in coeffs.iter_mut().rev().zip(
                    grand_products
                        .iter()
                        .rev()
                        .skip(1)
                        .chain(Some(F::one()).iter()),
                ) {
                    // s[0] = abc^-1
                    // a = c
                    // g = ab
                    let tmp = *a; // c
                    *a = *g;
                    a.mul_assign(&sub_inverses[chunk_id]); // a = ab*(abc^-1) = c^-1
                    sub_inverses[chunk_id].mul_assign(&tmp); // s[0] = (ab)^-1
                }
                child_worker.return_resources(cpu_unit).await;
            };
            let handle = worker.spawn_with_handle(fut).unwrap();
            handles.push(handle);
        }
        join_all(handles).await;

        Ok(())
    }

    pub fn pop_last(&mut self) -> Result<F, SynthesisError> {
        assert_eq!(Arc::strong_count(&self.coeffs.buf), 1);
        let mut last = SubVec::empty();
        let length = self.coeffs.len();
        assert!(length > 1);

        (self.coeffs, last) = self.coeffs.clone().split_at(length - 1);

        Ok(last.buf[0])
    }

    pub async fn clone_shifted_assuming_bitreversed(
        &self,
        by: usize,
        worker: Worker,
        is_background: bool,
    ) -> Result<Self, SynthesisError> {
        assert_eq!(self.coeffs.len(), self.coeffs.buf.len());
        let len = self.coeffs.len();
        assert!(by < len);
        let mut extended_clone = Vec::with_capacity(len + by);
        extended_clone.extend_from_slice(&self.coeffs.buf);
        let mut tmp = Self::from_values(extended_clone)?;
        tmp.bitreverse_enumeration(worker.child(), is_background)
            .await;

        let mut coeffs = tmp.into_coeffs();
        let tmp: Vec<_> = coeffs.drain(..by).collect();
        coeffs.extend(tmp);

        let mut tmp = Self::from_values(coeffs)?;
        tmp.bitreverse_enumeration(worker.child(), is_background)
            .await;

        Ok(tmp)
    }


    pub fn ifft(mut self, worker: &OldWorker) -> Polynomial<F, Coefficients>
    {
        debug_assert!(self.coeffs.len().is_power_of_two());        
        let mut coeffs = self.coeffs.deref_mut();
        crate::plonk::fft::fft::best_fft(coeffs, worker, &self.omegainv, self.exp, None);

        let minv = self.minv;
        worker.scope(coeffs.len(), |scope, chunk| {
            for v in coeffs.chunks_mut(chunk) {
                scope.spawn(move |_| {
                    for v in v {
                        v.mul_assign(&minv);
                    }
                });
            }
        });

        Polynomial::<F, Coefficients> {
            coeffs: self.coeffs,
            exp: self.exp,
            omega: self.omega,
            omegainv: self.omegainv,
            geninv: self.geninv,
            minv: self.minv,
            _marker: std::marker::PhantomData
        }
    }

    // pub async fn icoset_fft_for_generator(self, old_worker: Worker, is_background: bool, coset_generator: &F) -> Polynomial<F, Coefficients>
    pub async fn icoset_fft_for_generator(self, old_worker: &OldWorker, worker: Worker, is_background:bool, coset_generator: &F) -> Polynomial<F, Coefficients>
    {

        debug_assert!(self.coeffs.len().is_power_of_two());
        let geninv = coset_generator.inverse().expect("must exist");
        let mut res = self.ifft(old_worker);
        res.distribute_powers(worker.child(), is_background, geninv).await;

        res
    }
}

#[derive(Clone, Copy)]
pub enum Operation<F> {
    Add(F),
    Sub(F),
    Scale(F),
    Negate,
    Square,
    Pow(u64),
}

async fn op<F: PrimeField>(
    worker: Worker,
    is_background: bool,
    op: Operation<F>,
    this: SubVec<F>,
) {
    let num_cpus = worker.num_cpus();
    let mut this_chunks = this.clone().split_by_num_cpus(num_cpus);
    let chunk_size = this_chunks[0].len();
    let mut handles = vec![];

    for (child_worker, mut chunk) in this_chunks
        .into_iter()
        .map(|chunk| (worker.child(), chunk))
    {
        let fut = async move {
            let cpu_unit = child_worker.get_cpu_unit(is_background).await.await;
            let buf = chunk.deref_mut();
            for el in buf.iter_mut() {
                match op {
                    Operation::Scale(ref scaling) => el.mul_assign(scaling),
                    Operation::Negate => el.negate(),
                    Operation::Pow(power) => *el = el.pow(&[power]),
                    Operation::Add(ref constant) => el.add_assign(constant),
                    Operation::Sub(ref constant) => el.sub_assign(constant),
                    Operation::Square => el.square(),
                }
            }

            child_worker.return_resources(cpu_unit).await;
        };
        let handle = worker.spawn_with_handle(fut).unwrap();
        handles.push(handle);
    }
    join_all(handles).await;
}

#[derive(Clone, Copy)]
pub enum BinOperation<F> {
    AddAssign,
    AddAssignScaled(F),
    SubAssign,
    SubAssignScaled(F),
    MulAssign,
}

async fn bin_op_scaled<F: PrimeField>(
    worker: Worker,
    is_background: bool,
    op: BinOperation<F>,
    this: SubVec<F>,
    other: SubVec<F>,
) {
    let num_cpus = worker.num_cpus();
    assert_eq!(this.len(), other.len());

    let this_chunks = this.clone().split_by_num_cpus(num_cpus);
    let other_chunks = other.clone().split_by_num_cpus(num_cpus);

    let mut handles = vec![];
    for (child_worker, mut this_chunk, other_chunk) in this_chunks
        .into_iter()
        .zip(other_chunks.into_iter())
        .map(|(this_chunk, other_chunk)| (worker.child(), this_chunk, other_chunk))
    {
        let fut = async move {
            let cpu_unit = child_worker.get_cpu_unit(is_background).await.await;
            let this_buf = this_chunk.deref_mut();
            let other_buf = other_chunk.deref();
            for (t, o) in this_buf.iter_mut().zip(other_buf.iter()) {
                match op {
                    BinOperation::AddAssign => t.add_assign(o),
                    BinOperation::AddAssignScaled(ref scalar) => {
                        let mut tmp = scalar.clone();
                        tmp.mul_assign(o);
                        t.add_assign(&tmp);
                    },
                    BinOperation::SubAssign => t.sub_assign(o),
                    BinOperation::SubAssignScaled(ref scalar) => {
                        let mut tmp = scalar.clone();
                        tmp.mul_assign(o);
                        t.sub_assign(&tmp);
                    },
                    BinOperation::MulAssign => t.mul_assign(o),
                }
            }

            child_worker.return_resources(cpu_unit).await;
        };
        let handle = worker.spawn_with_handle(fut).unwrap();
        handles.push(handle);
    }
    join_all(handles).await;
}

pub async fn calculate_grand_product<F: PrimeField>(
    worker: Worker,
    is_background: bool,
    coeffs: SubVec<F>,
    result: SubVec<F>,
) {
    let num_cpus = worker.num_cpus();
    let mut sub_products = SubVec::new(vec![F::one(); num_cpus]);
    let mut coeffs_chunks = coeffs.clone().split_by_num_cpus(num_cpus);
    let mut result_chunks = result.clone().split_by_num_cpus(num_cpus);

    let mut handles = vec![];
    for (chunk_id, (child_worker, mut coeffs_chunk, mut result_chunk, mut sub_products)) in itertools::izip!(
        coeffs_chunks.into_iter(),
        result_chunks.into_iter())
        .map(|(coeffs_chunk, result_chunk)| {
            (
                worker.child(),
                coeffs_chunk,
                result_chunk,
                sub_products.clone()
            )
        })
        .enumerate()
    {
        let fut = async move {
            let cpu_unit = child_worker.get_cpu_unit(is_background).await.await;
            let coeffs = coeffs_chunk.deref_mut();
            let result = result_chunk.deref_mut();
            let sub_products = sub_products.deref_mut();

            for (r, c) in result.iter_mut().zip(coeffs.iter()) {
                sub_products[chunk_id].mul_assign(c);
                *r = sub_products[chunk_id];
            }

            child_worker.return_resources(cpu_unit).await;
        };
        let handle = worker.spawn_with_handle(fut).unwrap();
        handles.push(handle);
    }
    join_all(handles).await;

    let mut sub_products = sub_products.into_inner();
    // subproducts are [abc, def, xyz]

    // we do not need the last one
    sub_products.pop().expect("has at least one value");

    let mut tmp = F::one();
    for s in sub_products.iter_mut() {
        tmp.mul_assign(&s);
        *s = tmp;
    }

    let mut result_chunks = result.split_by_num_cpus(num_cpus);
    let mut handles = vec![];
    for (worker, mut result_chunk, sub_product) in result_chunks
        .into_iter().skip(1)
        .zip(sub_products.into_iter())
        .map(|(result_chunk, sub_product)| {
            (
                worker.child(),
                result_chunk,
                sub_product
            )
        })
    {
        let child_worker = worker.child();
        let fut = async move {
            let cpu_unit = child_worker.get_cpu_unit(is_background).await.await;
            let result = result_chunk.deref_mut();
            for r in result.iter_mut() {
                r.mul_assign(&sub_product);
            }

            child_worker.return_resources(cpu_unit).await;
        };
        let handle = worker.spawn_with_handle(fut).unwrap();
        handles.push(handle);
    }

    join_all(handles).await;
}


#[cfg(test)]
mod tests {
    use super::*;
    use crate::pairing::bn256::{Bn256, Fr};
    use crate::pairing::ff::Field;
    use futures::executor::block_on;

    #[test]
    fn test_new_polynoms() {
        let manager = ResourceManagerProxy::new(num_cpus::get_physical(), 0, 1);
        let worker = manager.create_worker();

        let coeffs1 = vec![Fr::one(), Fr::zero(), Fr::zero(), Fr::zero()];
        let coeffs2 = vec![Fr::one(); 8];
        let coeffs3: Vec<Fr> = (0..8).map(|x| Fr::from_str(&format!("{}", x+1)).unwrap()).collect();
        let values1 = vec![Fr::one(); 8];

        let mut poly1 = Polynomial::from_coeffs(coeffs1).unwrap();
        let mut poly2 = Polynomial::from_coeffs(coeffs2).unwrap();
        let mut poly3 = Polynomial::from_values(coeffs3).unwrap();
        let mut poly4 = Polynomial::from_values(values1).unwrap();

        let res = block_on(poly3.calculate_shifted_grand_product(worker.child(), false)).unwrap();
        dbg!(res.as_ref());


    }

//     #[test]
//     fn test_grand_product(){
//         use rand::{thread_rng, Rand};
//         use futures::executor::block_on;
//         let rng = &mut thread_rng();
//         let old_worker = OldWorker::new();
//         let manager = ResourceManagerProxy::new(num_cpus::get_physical(), 0, 1);
//         let worker = manager.create_worker();

//         let degree = 32;
//         let values = vec![Fr::rand(rng); degree];

//         let poly = Polynomial::from_values(values).unwrap();

//         // let expected = poly.calculate_grand_product(&old_worker).unwrap();
//         // let actual = block_on(calculate_grand_product(worker.child(), false, &poly)).unwrap();
//         // assert_eq!(&expected.coeffs[..], &actual.coeffs[..]);
        
        
//         let expected = poly.calculate_shifted_grand_product(&old_worker).unwrap();
//         let actual = block_on(calculate_shifted_grand_product(worker.child(), false, &poly)).unwrap();

//         for (e, a) in expected.coeffs[1..].iter().zip(actual.coeffs.iter()){
//             assert_eq!(e, a);
//         }
//         // assert_eq!(&expected.coeffs[..], &actual.coeffs.deref()[..]);

//     }
}