use crate::plonk::better_better_cs::cs::*;
use crate::SynthesisError;
use splitmut::SplitMut;
use std::{ iter, mem };


impl From<splitmut::SplitMutError> for SynthesisError {
    fn from(_splitmut_err: splitmut::SplitMutError) -> SynthesisError {
        SynthesisError::UnexpectedIdentity
    }
}


pub trait IdentifyFirstLast: Iterator + Sized {
    fn identify_first_last(self) -> Iter<Self>;
}

impl<I> IdentifyFirstLast for I where I: Iterator {
    fn identify_first_last(self) -> Iter<Self> {
        Iter(true, self.peekable())
    }
}

pub struct Iter<I>(bool, iter::Peekable<I>) where I: Iterator;

impl<I> Iterator for Iter<I> where I: Iterator {
    type Item = (bool, bool, I::Item);

    fn next(&mut self) -> Option<Self::Item> {
        let first = mem::replace(&mut self.0, false);
        self.1.next().map(|e| (first, self.1.peek().is_none(), e))
    }
}