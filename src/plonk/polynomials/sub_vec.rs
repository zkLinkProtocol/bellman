#![feature(get_mut_unchecked)]
use std::{
    ops::{Deref, DerefMut, Range},
    sync::Arc,
};

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct SubVec<T: Clone> {
    pub buf: Arc<Vec<T>>,
    pub range: Range<usize>,
}

impl<T: Clone> Deref for SubVec<T> {
    type Target = [T];
    fn deref(&self) -> &[T] {
        &self.buf[self.range.clone()]
    }
}

impl<T: Clone> DerefMut for SubVec<T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        let this = unsafe { Arc::get_mut_unchecked(&mut self.buf) };
        &mut this[self.range.clone()]
    }
}

impl<T: Clone> From<Arc<Vec<T>>> for SubVec<T> {
    fn from(input: Arc<Vec<T>>) -> Self {
        Self {
            range: 0..input.len(),
            buf: input,
        }
    }
}

impl<T: Clone> SubVec<T> {
    pub fn new(v: Vec<T>) -> Self {
        let range = 0..v.len();
        Self {
            buf: Arc::from(v),
            range,
        }
    }

    pub fn as_ptr(&self) -> *const T {
        self.buf[self.range.clone()].as_ptr()
    }

    // FIXME
    pub fn as_mut_ptr(&self) -> *mut T {
        self.as_ptr() as *mut T
    }

    pub fn into_inner(self) -> Vec<T> {
        let range = self.range;
        let result = Arc::try_unwrap(self.buf);

        match result {
            Err(result) => {                
                let start = std::time::Instant::now();
                let r = result[range].to_vec();
                // println!("subvec copy!! takes {}ms", start.elapsed().as_millis());
                r
            }
            Ok(mut result) => {
                if range.len() == result.len() {
                    result
                } else {
                    result.drain(range).collect()
                }
            }
        }
    }

    pub fn split_at(self, i: usize) -> (SubVec<T>, SubVec<T>) {
        let first = self.range.start..(self.range.start + i);
        let second = (self.range.start + i)..self.range.end;

        assert!(i <= self.range.len());

        let buf = self.buf.clone();
        (
            SubVec {
                buf: buf.clone(),
                range: first,
            },
            SubVec {
                buf: buf.clone(),
                range: second,
            },
        )
    }

    pub fn split_by_num_cpus(&self, num_cpus: usize) -> Vec<SubVec<T>> {
        if self.len() <= num_cpus{
            return vec![self.clone()]
        }
        let mut chunk_size = self.len() / num_cpus;
        if self.len() % num_cpus != 0 {
            chunk_size += 1;
        }

        self.split_by_chunk_size(chunk_size)
    }

    pub fn split_by_chunk_size(&self, chunk_size: usize) -> Vec<SubVec<T>> {
        let mut chunks = vec![];
        let mut remainder = self.clone();

        while remainder.len() > chunk_size {
            let (chunk, next) = remainder.split_at(chunk_size);
            remainder = next;
            chunks.push(chunk);
        }
        chunks.push(remainder);

        chunks
    }
    
    pub fn split_by_chunk_size_and_num_cpus(
        &self,
        chunk_size: usize,
        num_cpus: usize,
    ) -> Vec<SubVec<SubVec<T>>> {
        let chunks = self.split_by_chunk_size(chunk_size);

        let new_chunks = SubVec::new(chunks);

        new_chunks.split_by_num_cpus(num_cpus)
    }

    pub fn resize(&mut self, new_size: usize, el: T) {
        let size = self.len();
        if new_size == size {
            return;
        } else if new_size > size {
            // FIXME: this is so dangerous, we can only resize when
            // buffer len == range len
            // assert_eq!(self.buf.len(), self.range.len());
            let values = unsafe { Arc::get_mut_unchecked(&mut self.buf) };
            values.resize(new_size, el);
            self.range = 0..values.len();
        } else {
            self.truncate(new_size)
        }
    }

    pub fn truncate(&mut self, new_size: usize) {
        if new_size > self.len() {
            return;
        }
        let size = self.len();
        self.range = self.range.start..self.range.end - (size - new_size);
    }

    pub fn split_off(&mut self, at: usize) -> SubVec<T> {
        if at > self.len() {
            panic!("at > len");
        }

        if at == 0 {
            return self.clone();
        }

        let mut new = self.clone();
        self.range = self.range.start..at;
        new.range = at..new.range.end;

        new
    }

    pub fn pop(&mut self) -> Option<T> {
        if self.is_empty() {
            return None;
        }
        let last = self.deref()[self.len() - 1].clone();
        let new_end = self.range.end - 1;
        self.range = self.range.start..new_end;
        Some(last)
    }

    pub fn empty() -> Self {
        Self::new(vec![])
    }

    pub fn copy(&self) -> Self {
        Self::new(self.clone().into_inner())
    }
}

#[test]
fn test_subvec_utils() {
    let mut v : Vec<usize> = (0..32).collect();
    let mut sv = SubVec::new(v.clone());   

    v.resize(32, 1);
    sv.resize(32, 1);
    assert_eq!(&v, &sv[..]);

    v.resize(16, 1);
    sv.resize(16, 1);
    assert_eq!(&v, &sv[..]);
    
    // v.resize(64, 1);
    // sv.resize(64, 1);
    // assert_eq!(&v, &sv[..]);
    
    v.truncate(32);
    sv.truncate(32);
    assert_eq!(&v, &sv[..]);
    
    v.truncate(48);
    sv.truncate(48);
    assert_eq!(&v, &sv[..]);
    
    let e = v.split_off(16);
    let a = sv.split_off(16);
    assert_eq!(&e, &a[..]);
    assert_eq!(&v, &sv[..]);
    
    let e = v.pop().unwrap();
    let a = sv.pop().unwrap();
    assert_eq!(e, a);
    assert_eq!(&v, &sv[..]);
        
}
