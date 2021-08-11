pub mod signed_digit;
pub mod rw_lock;

pub use self::signed_digit::*;
pub use self::rw_lock::*;

use core::ops::Range;

// a representation of a continuos vector as either a single vector,
// or by a set of vectors backed by the continuous allocation
#[derive(Debug)]
pub enum ChunkableVector<T> {
    Single(Vec<T>),
    Multiple(Vec<Vec<T>>)
}

pub fn get_chunk_size(
    num_elements: usize,
    num_chunks: usize
) -> usize {
    let chunk_size = if num_elements <= num_chunks {
        1
    } else {
        if num_elements % num_chunks == 0 {
            num_elements / num_chunks
        } else {
            num_elements / num_chunks + 1
        }
    };

    chunk_size
}

pub fn get_ranges(
    num_elements: usize,
    chunk_size: usize
) -> Vec<Range<usize>> {
    if num_elements <= chunk_size {
        let range = 0..num_elements;
        return vec![range]
    } else {
        let mut result = vec![];
        let mut start = 0;
        loop {
            if num_elements <= chunk_size + start {
                let range = start..num_elements;
                result.push(range);
                return result;
            } else {
                let range = start..(start+chunk_size);
                result.push(range);
                start += chunk_size;
            }
        } 
    }
}

impl<T> ChunkableVector<T> {
    pub fn new(elements: Vec<T>) -> Self {
        // we do not support ZSTs
        assert!(std::mem::size_of::<T>() != 0);
        ChunkableVector::Single(elements)
    }

    pub fn split(&mut self, num_chunks: usize) {
        let new = match self {
            ChunkableVector::Single(ref mut elements) => {
                let mut elements = std::mem::replace(elements, vec![]);
                let chunk_size = get_chunk_size(elements.len(), num_chunks);
                if num_chunks == 1 || chunk_size == elements.len() {
                    ChunkableVector::Multiple(vec![elements])
                } else {
                    let mut result = Vec::with_capacity(num_chunks);
                    let mut remaining_elements = elements.len();
                    let mut remaining_capacity = elements.capacity();
                    let mut elements_ptr = elements.as_mut_ptr();
                    std::mem::forget(elements);
                    // let (mut elements_ptr, mut remaining_elements, mut remaining_capacity) = elements.into_raw_parts();
                    for _ in 0..(num_chunks-1) {
                        let beginning = elements_ptr;
                        let num_elements = chunk_size;
                        let capacity = chunk_size;

                        remaining_elements -= num_elements;
                        remaining_capacity -= capacity;
                        elements_ptr = unsafe {elements_ptr.add(num_elements)};

                        let chunk = unsafe { Vec::from_raw_parts(beginning, num_elements, capacity)};
                        result.push(chunk);
                    }
                    let final_chunk = unsafe { Vec::from_raw_parts(elements_ptr, remaining_elements, remaining_capacity)};
                    result.push(final_chunk);

                    ChunkableVector::Multiple(result)
                }
            },
            _ => {
                panic!("value is not a single chunk");
            }
        };

        *self = new;
    }

    pub fn split_with_chunk_size(&mut self, chunk_size: usize) {
        let new = match self {
            ChunkableVector::Single(ref mut elements) => {
                let mut elements = std::mem::replace(elements, vec![]);
                let mut num_chunks = elements.len() / chunk_size;
                if elements.len() % chunk_size != 0 {
                    num_chunks += 1;
                }
                if num_chunks == 1 || chunk_size == elements.len() {
                    ChunkableVector::Multiple(vec![elements])
                } else {
                    let mut result = Vec::with_capacity(num_chunks);
                    let mut remaining_elements = elements.len();
                    let mut remaining_capacity = elements.capacity();
                    let mut elements_ptr = elements.as_mut_ptr();
                    std::mem::forget(elements);
                    // let (mut elements_ptr, mut remaining_elements, mut remaining_capacity) = elements.into_raw_parts();
                    for _ in 0..(num_chunks-1) {
                        let beginning = elements_ptr;
                        let num_elements = chunk_size;
                        let capacity = chunk_size;

                        remaining_elements -= num_elements;
                        remaining_capacity -= capacity;
                        elements_ptr = unsafe {elements_ptr.add(num_elements)};

                        let chunk = unsafe { Vec::from_raw_parts(beginning, num_elements, capacity)};
                        result.push(chunk);
                    }
                    let final_chunk = unsafe { Vec::from_raw_parts(elements_ptr, remaining_elements, remaining_capacity)};
                    result.push(final_chunk);

                    ChunkableVector::Multiple(result)
                }
            },
            _ => {
                panic!("value is not a single chunk");
            }
        };

        *self = new;
    }

    pub fn merge(&mut self) {
        let new = match self {
            ChunkableVector::Multiple(ref mut chunks) => {
                if chunks.len() == 0 {
                    ChunkableVector::Single(vec![])
                } else {
                    let mut chunks = std::mem::replace(chunks, vec![]);
                    let num_elements = chunks.iter().map(|el| el.len()).sum();
                    let capacity = chunks.iter().map(|el| el.capacity()).sum();
                    for pair in chunks.windows(2) {
                        let first_num_elements = pair[0].len();
                        let first_ptr = pair[0].as_ptr();
                        let second_ptr = pair[1].as_ptr();
                        assert_eq!(unsafe {first_ptr.add(first_num_elements)}, second_ptr);
                    }
                    let mut first_el = chunks.drain(0..1).next().unwrap();
                    let elements_ptr = first_el.as_mut_ptr();
                    std::mem::forget(first_el);
                    std::mem::forget(chunks);
                    let single_vector = unsafe { Vec::from_raw_parts(elements_ptr, num_elements, capacity)};

                    ChunkableVector::Single(single_vector)
                }
            },
            _ => {
                panic!("value is not a multi-chunk");
            }
        };

        *self = new;
    }

    pub fn into_single(self) -> Vec<T> {
        match self {
            ChunkableVector::Single(elements) => {
                elements
            },
            this @ ChunkableVector::Multiple(..) => {
                let mut this = this;
                this.merge();

                this.into_single()
            }
        }
    }

    pub fn into_multiple(mut self) -> Vec<VectorChunk<T>> {
        match self {
            ChunkableVector::Multiple(chunks) => {
                let mut result = vec![];
                for c in chunks.into_iter() {
                    let el = VectorChunk(c);
                    result.push(el);
                }

                result
            },
            this @ ChunkableVector::Single(..) => {
                panic!("value is not a multi-chunk");
            }
        }
    }
}

pub struct VectorChunk<T>(Vec<T>);

impl<T> AsRef<Vec<T>> for ChunkableVector<T> {
    fn as_ref(&self) -> &Vec<T> {
        match self {
            ChunkableVector::Single(ref elements) => {
                elements
            },
            ChunkableVector::Multiple(..) => {
                panic!("value is not a single chunk");
            }
        }
    }
}

impl<T> AsMut<Vec<T>> for ChunkableVector<T> {
    fn as_mut(&mut self) -> &mut Vec<T> {
        match self {
            ChunkableVector::Single(ref mut elements) => {
                elements
            },
            ChunkableVector::Multiple(..) => {
                panic!("value is not a single chunk");
            }
        }
    }
}

impl<T> AsRef<Vec<Vec<T>>> for ChunkableVector<T> {
    fn as_ref(&self) -> &Vec<Vec<T>> {
        match self {
            ChunkableVector::Single(..) => {
                panic!("value is not a multi-chunk");
            },
            ChunkableVector::Multiple(ref chunks) => {
                chunks
            }
        }
    }
}

impl<T> AsMut<Vec<Vec<T>>> for ChunkableVector<T> {
    fn as_mut(&mut self) -> &mut Vec<Vec<T>> {
        match self {
            ChunkableVector::Single(..) => {
                panic!("value is not a multi-chunk");
            },
            ChunkableVector::Multiple(ref mut chunks) => {
                chunks
            }
        }
    }
}

// impl<T> Drop for ChunkableVector<T> {
//     fn drop(&mut self) {
//         println!("Drop");
//         match self {
//             ChunkableVector::Single(_) => {},
//             ChunkableVector::Multiple(..) => {
//                 panic!("Must merge before dropping");
//             }
//         }
//     }
// }

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_split_and_merge() {
        let vec = vec![0usize; 1024];
        let cap = vec.capacity();
        let mut vec = ChunkableVector::new(vec);
        vec.split(16);
        vec.merge();

        let res = vec.into_single();
        assert_eq!(res.len(), 1024);
        assert_eq!(res.capacity(), cap);   
    }

    #[test]
    fn test_empty_split_and_merge() {
        let vec: Vec<usize> = vec![];
        let cap = vec.capacity();
        let mut vec = ChunkableVector::new(vec);
        vec.split(16);
        vec.merge();

        let res = vec.into_single();
        assert_eq!(res.len(), 0);
        assert_eq!(res.capacity(), cap);   
    }
}