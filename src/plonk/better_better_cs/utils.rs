use crate::pairing::ff::PrimeField;
use crate::worker::Worker;

pub trait FieldBinop<F: PrimeField>: 'static + Copy + Clone + Send + Sync + std::fmt::Debug {
    fn apply(&self, dest: &mut F, source: &F);
}

pub(crate) fn binop_over_slices<F: PrimeField, B: FieldBinop<F>>(worker: &Worker, binop: &B, dest: &mut [F], source: &[F]) {
    assert_eq!(dest.len(), source.len());
    worker.scope(dest.len(), |scope, chunk| {
        for (dest, source) in dest.chunks_mut(chunk)
                            .zip(source.chunks(chunk)) {
            scope.spawn(move |_| {
                for (dest, source) in dest.iter_mut().zip(source.iter()) {
                    binop.apply(dest, source);
                }
            });
        }
    });
}

#[derive(Clone, Copy, Debug)]
pub struct BinopAddAssign;

impl<F: PrimeField> FieldBinop<F> for BinopAddAssign {
    #[inline(always)]
    fn apply(&self, dest: &mut F, source: &F) {
        dest.add_assign(source);
    }   
}

#[derive(Clone, Copy, Debug)]
pub struct BinopAddAssignScaled<F: PrimeField>{
    pub scale: F
}

impl<F: PrimeField> BinopAddAssignScaled<F> {
    pub fn new(scale: F) -> Self {
        Self {
            scale
        }
    }
}

impl<F: PrimeField> FieldBinop<F> for BinopAddAssignScaled<F> {
    #[inline(always)]
    fn apply(&self, dest: &mut F, source: &F) {
        let mut tmp = self.scale;
        tmp.mul_assign(&source);

        dest.add_assign(&tmp);
    }   
}