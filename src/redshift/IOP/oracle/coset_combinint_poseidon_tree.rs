use crate::pairing::ff::{Field, PrimeField, PrimeFieldRepr};
use crate::multicore::Worker;
use super::*;
use crate::redshift::IOP::hashes::poseidon::{PoseidonHashParams, PoseidonR2C1};
use crate::redshift::IOP::hashes::poseidon::params::Bn256PoseidonParams;
use crate::redshift::IOP::hashes::poseidon::group_hash::BlakeHasher;
use crate::pairing::bn256::{Bn256, Fr};


pub struct PoseidonBN256Tree<'a> {
    pub size: usize,
    pub values_per_leaf: usize,
    pub nodes: Vec<Fr>,
    pub params: &'a Bn256PoseidonParams,
}


impl<'a> PoseidonBN256Tree<'a> {
    
    fn hash_into_leaf(values: &[Fr], params: &Bn256PoseidonParams) -> Fr {
        let mut hasher = PoseidonR2C1::new(params);
        for value in values.iter() {
            hasher.absorb(*value);
        }
        hasher.squeeze()
    }

    fn size(&self) -> usize {
        self.size
    }

    fn create(values: &[Fr], size: usize, values_per_leaf: usize, params: &'a Bn256PoseidonParams) -> Self {

        assert!(values_per_leaf.is_power_of_two());
        assert!(values.len() == size * values_per_leaf);

        let num_nodes = size;
        let mut nodes = vec![Fr::zero(); num_nodes];

        let worker = Worker::new();
        let mut leaf_hashes = vec![Fr::zero(); num_nodes];
        {
            worker.scope(leaf_hashes.len(), |scope, chunk| {
                for (i, lh) in leaf_hashes.chunks_mut(chunk)
                                .enumerate() {
                    scope.spawn(move |_| {
                        let base_idx = i*chunk;
                        for (j, lh) in lh.iter_mut().enumerate() {
                            let idx = base_idx + j;
                            let values_start = idx * values_per_leaf;
                            let values_end = values_start + values_per_leaf;
                            *lh = Self::hash_into_leaf(&values[values_start..values_end], params);
                        }
                    });
                }
            });
        }

        // leafs are now encoded and hashed, so let's make a tree

        let num_levels = log2_floor(num_nodes) as usize;
        let mut nodes_for_hashing = &mut nodes[..];

        // separately hash last level, which hashes leaf hashes into first nodes
        {
            let _level = num_levels-1;
            let inputs = &mut leaf_hashes[..];
            let (_, outputs) = nodes_for_hashing.split_at_mut(nodes_for_hashing.len()/2);
            assert!(outputs.len() * 2 == inputs.len());
            assert!(outputs.len().is_power_of_two());

            worker.scope(outputs.len(), |scope, chunk| {
                for (o, i) in outputs.chunks_mut(chunk)
                                .zip(inputs.chunks(chunk*2)) {
                    scope.spawn(move |_| {
                        for (o, i) in o.iter_mut().zip(i.chunks(2)) {
                            let mut hasher = PoseidonR2C1::new(params);
                            hasher.absorb(i[0]);
                            hasher.absorb(i[1]);
                            *o = hasher.squeeze();
                        }
                    });
                }
            });
        }

        for _ in (0..(num_levels-1)).rev() {
            // do the trick - split
            let (next_levels, inputs) = nodes_for_hashing.split_at_mut(nodes_for_hashing.len()/2);
            let (_, outputs) = next_levels.split_at_mut(next_levels.len() / 2);
            assert!(outputs.len() * 2 == inputs.len());
            assert!(outputs.len().is_power_of_two());

            worker.scope(outputs.len(), |scope, chunk| {
                for (o, i) in outputs.chunks_mut(chunk)
                                .zip(inputs.chunks(chunk*2)) {
                    scope.spawn(move |_| {
                        for (o, i) in o.iter_mut().zip(i.chunks(2)) {
                            let mut hasher = PoseidonR2C1::new(params);
                            hasher.absorb(i[0]);
                            hasher.absorb(i[1]);
                            *o = hasher.squeeze();
                        }
                    });
                }
            });

            nodes_for_hashing = next_levels;
        }

        Self {
            size: size,
            values_per_leaf: values_per_leaf,
            nodes: nodes,
            params: params,
        }
    }
}

#[test]
fn test_poseidon_tree() {

    use std::time::{Duration, Instant};

    const SIZE: usize = 1048576;
    const VALUES_PER_LEAF: usize = 4;
    let params = Bn256PoseidonParams::new_2_into_1::<BlakeHasher>();
    
    let values : Vec<Fr> = (0..(SIZE * VALUES_PER_LEAF)).scan(Fr::multiplicative_generator(), |cur, _| {
        let res = cur.clone();
        cur.double();
        Some(res)
    }).collect();

    let now = Instant::now();
    let tree = PoseidonBN256Tree::create(&values[..], SIZE, VALUES_PER_LEAF, &params);

    println!("Poseidon MerkleTreeConstruction of size {} took {}s", SIZE, now.elapsed().as_secs());
}

