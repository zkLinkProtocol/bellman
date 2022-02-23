use crate::SynthesisError;
use crate::plonk::domains::*;
use crate::plonk::fft::cooley_tukey_ntt::bitreverse;
use futures::future::join_all;
use pairing::ff::PrimeField;
use heavy_ops_service::*;
use std::sync::Arc;
use crate::multicore::Worker as OldWorker;
pub trait PolynomialForm: Sized + Copy + Clone {}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum Coefficients {}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum Values {}

impl PolynomialForm for Coefficients {}
impl PolynomialForm for Values {}

#[derive(PartialEq, Eq, Debug)]
pub struct Polynomial<F: PrimeField, P: PolynomialForm> {
    coeffs: Arc<Vec<F>>,
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
            coeffs: Default::default(),
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
        let len = self.coeffs.len();
        let mut coeffs = vec![F::zero(); len];
        // TODO
        unsafe { std::ptr::copy(self.coeffs.as_ptr(), coeffs.as_mut_ptr(), len) };
        Self {
            coeffs: Arc::new(coeffs),
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
        self.coeffs.as_ref()
    }

    pub fn as_mut(&mut self) -> &mut [F] {
        // FIXME
        unsafe{std::slice::from_raw_parts_mut(self.coeffs.as_ptr() as *mut F, self.coeffs.len())}
    }

    fn borrow_mut(&self) -> &mut Self{
        unsafe{&mut *(self as *const Self as  *mut Self)}
    }

    pub fn into_coeffs(self) -> Vec<F> {
        let num_items = self.coeffs.len();
        let mut coeffs = vec![F::zero(); num_items];
        unsafe{std::ptr::copy(self.coeffs.as_ptr(), coeffs.as_mut_ptr(), num_items)};

        coeffs        
    }

    pub fn arc_coeffs(&self) -> Arc<Vec<F>> {        
        self.coeffs.clone()
    }
    
    pub fn arc_clone(&self) -> Self {        
        Self{
            coeffs: self.coeffs.clone(),
            exp: self.exp,
            omega: self.omega,
            omegainv: self.omegainv,
            geninv: self.geninv,
            minv: self.minv,
            _marker: std::marker::PhantomData,
        }
    }

    pub async fn distribute_powers(&mut self, worker: Worker, is_background: bool, g: F) {
        let num_cpus = worker.num_cpus();
        let num_items = self.coeffs.len();
        let chunk_size = num_items / num_cpus;
        let mut handles = vec![];
        for (chunk_id, (child_worker, coeffs, chunk)) in self
            .coeffs
            .chunks(chunk_size)
            .map(|c| (worker.child(), self.coeffs.clone(), c))
            .enumerate()
        {
            let chunk_len = chunk.len();
            let start = chunk_id * chunk_size;
            let end = start + chunk_len;
            let range = start..end;
            let fut = async move {
                let cpu_unit = child_worker.get_cpu_unit(is_background).await.await;
                let buf = unsafe {
                    std::slice::from_raw_parts_mut(coeffs[range].as_ptr() as *mut F, chunk_len)
                };
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

    // FIXME
    pub fn reuse_allocation<PP: PolynomialForm>(&self, other: &Polynomial<F, PP>) {
        assert_eq!(self.coeffs.len(), other.coeffs.len());
        let coeffs = unsafe { Arc::get_mut_unchecked(&mut self.borrow_mut().coeffs) };
        coeffs.copy_from_slice(&other.coeffs); // TODO multicore
    }

    pub async fn bitreverse_enumeration(&mut self, worker: Worker, is_background: bool) {
        let coeffs = unsafe { Arc::get_mut_unchecked(&mut self.coeffs) };
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

        // while it's unsafe we don't care cause swapping is always one to one

        let num_cpus = worker.num_cpus();
        let num_items = coeffs.len();
        let chunk_size = num_items / num_cpus;
        let mut handles = vec![];
        for (chunk_id, (child_worker, coeffs, chunk)) in self
            .coeffs
            .chunks(chunk_size)
            .map(|c| (worker.child(), self.coeffs.clone(), c))
            .enumerate()
        {
            let chunk_len = chunk.len();
            let fut = async move {
                let cpu_unit = child_worker.get_cpu_unit(is_background).await.await;
                let start = chunk_id * chunk_size;
                let end = start + chunk_len;
                let range = start..end;
                let buf =
                    unsafe { std::slice::from_raw_parts_mut(coeffs.as_ptr() as *mut F, total_len) };
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
        debug_assert!(self.coeffs.len().is_power_of_two());

        if factor == 1 {
            return Ok(());
        }
        let next_power_of_two = factor.next_power_of_two();
        if factor != next_power_of_two {
            return Err(SynthesisError::Unsatisfiable);
        }

        let new_size = self.coeffs.len() * factor;
        let coeffs = unsafe { Arc::get_mut_unchecked(&mut self.coeffs) };
        coeffs.resize(new_size, F::zero());
        // self.coeffs.resize(new_size, F::zero());

        let domain = Domain::new_for_size(new_size as u64)?;
        self.exp = domain.power_of_two as u32;
        let m = domain.size as usize;
        self.omega = domain.generator;
        self.omegainv = self.omega.inverse().unwrap();
        self.minv = F::from_str(&format!("{}", m)).unwrap().inverse().unwrap();

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
        let coeffs = unsafe { Arc::get_mut_unchecked(&mut self.coeffs) };
        coeffs.resize(new_size, F::zero());
        // self.coeffs.resize(new_size, F::zero());

        let domain = Domain::new_for_size(new_size as u64)?;
        self.exp = domain.power_of_two as u32;
        let m = domain.size as usize;
        self.omega = domain.generator;
        self.omegainv = self.omega.inverse().unwrap();
        self.minv = F::from_str(&format!("{}", m)).unwrap().inverse().unwrap();

        Ok(())
    }

    pub fn pad_to_domain(&mut self) -> Result<(), SynthesisError> {
        let domain = Domain::<F>::new_for_size(self.coeffs.len() as u64)?;
        let coeffs = unsafe { Arc::get_mut_unchecked(&mut self.coeffs) };
        coeffs.resize(domain.size as usize, F::zero());
        // self.coeffs.resize(domain.size as usize, F::zero());

        Ok(())
    }

    pub fn clone_padded_to_domain(&self) -> Result<Self, SynthesisError> {
        let mut padded = self.clone();
        let domain = Domain::<F>::new_for_size(self.coeffs.len() as u64)?;
        let coeffs = unsafe { Arc::get_mut_unchecked(&mut padded.coeffs) };
        coeffs.resize(domain.size as usize, F::zero());
        // padded.coeffs.resize(domain.size as usize, F::zero());

        Ok(padded)
    }

    pub fn trim_to_degree(&mut self, degree: usize) -> Result<(), SynthesisError> {
        let size = self.coeffs.len();
        if size <= degree + 1 {
            return Ok(());
        }
        let coeffs = unsafe { Arc::get_mut_unchecked(&mut self.coeffs) };
        coeffs.truncate(degree + 1);
        coeffs.resize(size, F::zero());

        Ok(())
    }
}

impl<F: PrimeField> Polynomial<F, Coefficients> {
    pub fn new_for_size(size: usize) -> Result<Polynomial<F, Coefficients>, SynthesisError> {
        let coeffs = vec![F::zero(); size];

        Self::from_coeffs(coeffs)
    }

    pub fn from_coeffs(mut coeffs: Vec<F>) -> Result<Polynomial<F, Coefficients>, SynthesisError> {
        let coeffs_len = coeffs.len();

        let domain = Domain::new_for_size(coeffs_len as u64)?;
        let exp = domain.power_of_two as u32;
        let m = domain.size as usize;
        let omega = domain.generator;

        coeffs.resize(m, F::zero());

        Ok(Polynomial::<F, Coefficients> {
            coeffs: Arc::new(coeffs),
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
        let mut coeffs = unsafe {
            Vec::from_raw_parts(
                self.coeffs.as_ptr() as *mut F,
                self.coeffs.len(),
                self.coeffs.len(),
            )
        };

        let (mut num_parts, last_size) = if coeffs.len() % size == 0 {
            let num_parts = coeffs.len() / size;

            (num_parts, 0)
        } else {
            let num_parts = coeffs.len() / size;
            let last_size = coeffs.len() - num_parts * size;

            (num_parts, last_size)
        };

        let mut rev_results = Vec::with_capacity(num_parts);

        if last_size != 0 {
            let drain = coeffs.split_off(coeffs.len() - last_size);
            rev_results.push(drain);
            num_parts -= 1;
        }

        for _ in 0..num_parts {
            let drain = coeffs.split_off(coeffs.len() - size);
            rev_results.push(drain);
        }

        let mut results = Vec::with_capacity(num_parts);

        for c in rev_results.into_iter().rev() {
            let poly = Polynomial::<F, Coefficients>::from_coeffs(c)?;
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
        let num_items = self.coeffs.len();
        let chunk_size = num_items / num_cpus;
        let mut handles = vec![];
        for (chunk_id, (child_worker, coeffs, chunk)) in self
            .coeffs
            .chunks(chunk_size)
            .map(|c| (worker.child(), self.coeffs.clone(), c))
            .enumerate()
        {
            let chunk_len = chunk.len();
            let start = chunk_id * chunk_size;
            let end = start + chunk_len;
            let range = start..end;
            let fut = async move {
                let cpu_unit = child_worker.get_cpu_unit(is_background).await.await;
                let buf = unsafe {
                    std::slice::from_raw_parts_mut(coeffs[range].as_ptr() as *mut F, chunk_len)
                };

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

    pub fn from_values(mut values: Vec<F>) -> Result<Polynomial<F, Values>, SynthesisError> {
        let coeffs_len = values.len();

        let domain = Domain::new_for_size(coeffs_len as u64)?;
        let exp = domain.power_of_two as u32;
        let m = domain.size as usize;
        let omega = domain.generator;

        values.resize(m, F::zero());

        Ok(Polynomial::<F, Values> {
            coeffs: Arc::new(values),
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
            coeffs: values,
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

        result.copy_from_slice(&self.coeffs[start..end]);

        // unsafe { result.set_len(new_size)};
        // let copy_to_start_pointer: *mut F = result[..].as_mut_ptr();
        // let copy_from_start_pointer: *const F = self.coeffs[start..end].as_ptr();

        // unsafe { std::ptr::copy_nonoverlapping(copy_from_start_pointer, copy_to_start_pointer, new_size) };

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
        let mut values: Vec<_> = self.coeffs.drain(by..).collect();

        for c in self.coeffs.into_iter() {
            values.push(c);
        }

        Polynomial::from_values(values)
    }

    pub async fn calculate_shifted_grand_product(
        &self,
        worker: Worker,
        is_background: bool,
    ) -> Result<Polynomial<F, Values>, SynthesisError> {
        let num_items = self.coeffs.len();
        let mut result = vec![F::zero(); num_items + 1];
        let result_ptr = result.as_mut_ptr();
        let result_len = result.len();
        result[0] = F::one();
        std::mem::forget(result);
        let result = unsafe {
            // ignore first elem
            let len = result_len - 1;
            Vec::from_raw_parts(result_ptr.add(1), len, len)
        };
        let result = Arc::new(result);
        calculate_grand_product(worker, is_background, self.coeffs.clone(), result.clone()).await;
        std::mem::forget(result);
        let result = unsafe {
            // get first elem back
            let len = result_len;
            Vec::from_raw_parts(result_ptr, len, len)
        };
        Polynomial::from_values(result)
    }

    pub async fn calculate_grand_product(
        &self,
        worker: Worker,
        is_background: bool,
    ) -> Result<Polynomial<F, Values>, SynthesisError> {
        let result = Arc::new(vec![F::zero(); self.coeffs.len()]);
        calculate_grand_product(worker, is_background, self.coeffs.clone(), result.clone()).await;
        let result = Arc::try_unwrap(result).expect("live arc");
        Polynomial::from_values(result)
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
        &self, // FIXME
        worker: Worker,
        is_background: bool,
    ) -> Result<(), SynthesisError> {
        let num_cpus = worker.num_cpus();
        let num_items = self.coeffs.len();
        dbg!(num_items);
        let grand_products = Arc::new(vec![F::one(); num_items]);
        let sub_products = Arc::new(vec![F::one(); num_cpus]);
        let mut chunk_size = num_items / num_cpus;
        if num_items % num_cpus != 0{
            chunk_size += 1;
        }
        let mut handles = vec![];
        for (chunk_id, (child_worker, coeffs, grand_products, sub_products, chunk_len)) in self
            .coeffs
            .chunks(chunk_size)
            .map(|chunk| {
                (
                    worker.child(),
                    self.coeffs.clone(),
                    grand_products.clone(),
                    sub_products.clone(),
                    chunk.len(),
                )
            })
            .enumerate()
        {
            assert!(chunk_id < num_cpus);
            let start = chunk_id * chunk_size;
            let end = start + chunk_len;
            let range = start..end;
            let fut = async move {
                let cpu_unit = child_worker.get_cpu_unit(is_background).await.await;
                let coeffs = unsafe {
                    std::slice::from_raw_parts(
                        coeffs[range.clone()].as_ptr(),
                        chunk_len,
                    )
                };

                let grand_products = unsafe {
                    std::slice::from_raw_parts_mut(
                        grand_products[range].as_ptr() as *mut F,
                        chunk_len,
                    )
                };
                let sub_products = unsafe {
                    std::slice::from_raw_parts_mut(
                        sub_products.as_ptr() as *mut F,
                        sub_products.len(),
                    )
                };
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
        for sub in sub_products.iter() {
            full_grand_product.mul_assign(sub);
        }

        let product_inverse = full_grand_product
            .inverse()
            .ok_or(SynthesisError::DivisionByZero)?;

        // now let's get [abc^-1, def^-1, ..., xyz^-1];
        let mut sub_inverses = vec![F::one(); num_cpus];
        for (i, s) in sub_inverses.iter_mut().enumerate() {
            let mut tmp = product_inverse;
            for (j, p) in sub_products.iter().enumerate() {
                if i == j {
                    continue;
                }
                tmp.mul_assign(&p);
            }

            *s = tmp;
        }

        let sub_inverses = Arc::new(sub_inverses);

        let mut handles = vec![];
        for (chunk_id, (child_worker, coeffs, grand_products, sub_inverses, chunk_len)) in self
            .coeffs
            .chunks(chunk_size)
            .map(|chunk| {
                (
                    worker.child(),
                    self.coeffs.clone(),
                    grand_products.clone(),
                    sub_inverses.clone(),
                    chunk.len(),
                )
            })
            .enumerate()
        {
            let start = chunk_id * chunk_size;
            let end = start + chunk_len;
            let range = start..end;
            let fut = async move {
                let cpu_unit = child_worker.get_cpu_unit(is_background).await.await;
                let coeffs = unsafe {
                    std::slice::from_raw_parts_mut(
                        coeffs[range.clone()].as_ptr() as *mut F,
                        chunk_len,
                    )
                };
                let grand_products = unsafe {
                    std::slice::from_raw_parts_mut(
                        grand_products[range].as_ptr() as *mut F,
                        chunk_len,
                    )
                };
                let sub_inverses = unsafe {
                    std::slice::from_raw_parts_mut(
                        sub_inverses.as_ptr() as *mut F,
                        sub_inverses.len(),
                    )
                };

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
        let coeffs = unsafe { Arc::get_mut_unchecked(&mut self.coeffs) };
        let last = coeffs.pop().ok_or(SynthesisError::AssignmentMissing)?;

        Ok(last)
    }

    pub async fn clone_shifted_assuming_bitreversed(
        &self,
        by: usize,
        worker: Worker,
        is_background: bool,
    ) -> Result<Self, SynthesisError> {
        let len = self.coeffs.len();
        assert!(by < len);
        let mut extended_clone = Vec::with_capacity(len + by);
        extended_clone.extend_from_slice(&self.coeffs);
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
        let mut coeffs = unsafe{Arc::get_mut_unchecked(&mut self.coeffs)};
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
    this: Arc<Vec<F>>,
) {
    let num_cpus = worker.num_cpus();
    let num_items = this.len();
    let chunk_size = num_items / num_cpus;
    let mut handles = vec![];
    for (chunk_id, (child_worker, coeffs, chunk)) in this
        .chunks(chunk_size)
        .map(|c| (worker.child(), this.clone(), c))
        .enumerate()
    {
        let chunk_len = chunk.len();
        let start = chunk_id * chunk_size;
        let end = start + chunk_len;
        let range = start..end;
        let fut = async move {
            let cpu_unit = child_worker.get_cpu_unit(is_background).await.await;
            let buf = unsafe {
                std::slice::from_raw_parts_mut(coeffs[range].as_ptr() as *mut F, chunk_len)
            };
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
    this: Arc<Vec<F>>,
    other: Arc<Vec<F>>,
) {
    let num_cpus = worker.num_cpus();
    let num_items = other.len();
    let chunk_size = num_items / num_cpus;
    let mut handles = vec![];
    for (chunk_id, (child_worker, this, other, chunk)) in other
        .chunks(chunk_size)
        .map(|chunk| (worker.child(), this.clone(), other.clone(), chunk))
        .enumerate()
    {
        let chunk_len = chunk.len();
        let start = chunk_id * chunk_size;
        let end = start + chunk_len;
        let range = start..end;
        let fut = async move {
            let cpu_unit = child_worker.get_cpu_unit(is_background).await.await;
            let this_buf = unsafe {
                std::slice::from_raw_parts_mut(this[range.clone()].as_ptr() as *mut F, chunk_len)
            };
            let other_buf = unsafe {
                std::slice::from_raw_parts_mut(other[range].as_ptr() as *mut F, chunk_len)
            };
            for (t, o) in this_buf.iter_mut().zip(other_buf) {
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
    coeffs: Arc<Vec<F>>,
    result: Arc<Vec<F>>,
) {
    let num_cpus = worker.num_cpus();
    let num_items = coeffs.len();
    let mut sub_products = Arc::new(vec![F::one(); num_cpus]);
    let mut chunk_size = num_items / num_cpus;
    if num_items % num_cpus != 0 {
        chunk_size +=1 ;
    }
    let mut handles = vec![];
    for (chunk_id, (child_worker, result, coeffs, sub_products, chunk_len)) in coeffs
        .chunks(chunk_size)
        .map(|chunk| {
            (
                worker.child(),
                result.clone(),
                coeffs.clone(),
                sub_products.clone(),
                chunk.len(),
            )
        })
        .enumerate()
    {
        let start = chunk_id * chunk_size;
        let end = start + chunk_len;
        let range = start..end;
        let fut = async move {
            let cpu_unit = child_worker.get_cpu_unit(is_background).await.await;
            let coeffs = unsafe {
                std::slice::from_raw_parts_mut(coeffs[range.clone()].as_ptr() as *mut F, chunk_len)
            };
            let result = unsafe {
                std::slice::from_raw_parts_mut(result[range].as_ptr() as *mut F, chunk_len)
            };
            let sub_products = unsafe {
                std::slice::from_raw_parts_mut(sub_products.as_ptr() as *mut F, sub_products.len())
            };

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

    {
        let sub_products = unsafe { Arc::get_mut_unchecked(&mut sub_products) };
        // subproducts are [abc, def, xyz]

        // we do not need the last one
        sub_products.pop().expect("has at least one value");

        let mut tmp = F::one();
        for s in sub_products.iter_mut() {
            tmp.mul_assign(&s);
            *s = tmp;
        }

        std::mem::forget(sub_products);
    }

    let mut handles = vec![];
    for (chunk_id, (worker, result, sub_products, chunk_len)) in result
        .chunks(chunk_size)
        .map(|chunk| {
            (
                worker.child(),
                result.clone(),
                sub_products.clone(),
                chunk.len(),
            )
        })
        .enumerate()
        .skip(1)
    {
        let child_worker = worker.child();
        let fut = async move {
            let start = chunk_id * chunk_len;
            let end = start + chunk_len;
            let range = start..end;
            let cpu_unit = child_worker.get_cpu_unit(is_background).await.await;
            let result = unsafe {
                std::slice::from_raw_parts_mut(result[range].as_ptr() as *mut F, chunk_len)
            };
            let sub_products = unsafe {
                std::slice::from_raw_parts_mut(sub_products.as_ptr() as *mut F, sub_products.len())
            };
            for r in result.iter_mut() {
                r.mul_assign(&sub_products[chunk_id - 1]);
            }

            child_worker.return_resources(cpu_unit).await;
        };
        let handle = worker.spawn_with_handle(fut).unwrap();
        handles.push(handle);
    }

    join_all(handles).await;
}
