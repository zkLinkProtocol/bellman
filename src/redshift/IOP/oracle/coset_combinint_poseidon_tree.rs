use crate::pairing::ff::{Field, PrimeField, PrimeFieldRepr};
use crate::multicore::Worker;
use super::*;
use crate::redshift::IOP::hashes::poseidon::{PoseidonHashParams, PoseidonR2C1};
use crate::redshift::IOP::hashes::poseidon::*;
use crate::redshift::IOP::hashes::poseidon::group_hash::BlakeHasher;
use crate::pairing::bn256::{Bn256, Fr};
use crate::pairing::bls12_381::Bls12;
use crate::pairing::ff::ScalarEngine;

#[derive(Clone, Copy, PartialEq)]
pub enum TreeType {
    Tree2To1,
    Tree4To1,
}


pub struct PoseidonBN256Tree<'a, Params: PoseidonHashParams> {
    pub size: usize,
    pub values_per_leaf: usize,
    pub nodes: Vec<Params::Fr>,
    pub params: &'a Params,
    pub tree_type: TreeType,
}


impl<'a, Params: PoseidonHashParams> PoseidonBN256Tree<'a, Params> {
    
    fn hash_into_leaf(values: &[Params::Fr], params: &Params, tree_type: TreeType) -> Params::Fr {
        
        let res = match tree_type {
            TreeType::Tree2To1 => {
                let mut hasher = PoseidonR2C1::new(params);
                for value in values.iter() {
                    hasher.absorb(*value);
                }
                hasher.squeeze()
            }
            TreeType::Tree4To1 => {
                let mut hasher = PoseidonR4C1::new(params);
                for value in values.iter() {
                    hasher.absorb(*value);
                }
                hasher.squeeze()
            }
        };

        res
    }

    fn size(&self) -> usize {
        self.size
    }

    fn create(values: &[Params::Fr], size: usize, values_per_leaf: usize, params: &'a Params, tree_type: TreeType) -> Self {

        let tree = match tree_type {
            TreeType::Tree2To1 => Self::create_2_to_1_tree(values, size, values_per_leaf, params),
            TreeType::Tree4To1 => Self::create_4_to_1_tree(values, size, values_per_leaf, params)
        };

        tree
    }

    fn create_4_to_1_tree(values: &[Params::Fr], size: usize, values_per_leaf: usize, params: &'a Params) -> Self {

        assert!(values_per_leaf.is_power_of_two());
        assert!(values.len() == size * values_per_leaf);

        let num_nodes = size;
        let mut nodes = vec![Params::Fr::zero(); num_nodes];

        let worker = Worker::new();
        let mut leaf_hashes = vec![Params::Fr::zero(); num_nodes];
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
                            *lh = Self::hash_into_leaf(&values[values_start..values_end], params, TreeType::Tree4To1);
                        }
                    });
                }
            });
        }

        // leafs are now encoded and hashed, so let's make a tree

        let mut input_size = size;
        let mut offset = 0;

        // separately hash last level, which hashes leaf hashes into first nodes
        {
            let inputs = &mut leaf_hashes[..];
            let outputs = &mut nodes[0..input_size / 4];
            assert!(outputs.len() * 4 == inputs.len());
            assert!(outputs.len().is_power_of_two());

            worker.scope(outputs.len(), |scope, chunk| {
                for (o, i) in outputs.chunks_mut(chunk)
                                .zip(inputs.chunks(chunk*4)) {
                    scope.spawn(move |_| {
                        for (o, i) in o.iter_mut().zip(i.chunks(4)) {
                            let mut hasher = PoseidonR4C1::new(params);
                            hasher.absorb(i[0]);
                            hasher.absorb(i[1]);
                            *o = hasher.squeeze();
                        }
                    });
                }
            });

            input_size /= 4;
        }

        while input_size > 1 {
            
            let (inputs_part, outputs_part) = nodes.split_at_mut(offset + input_size);
            
            let inputs = &inputs_part[offset..];
            offset += input_size;
            input_size /= 4;
            let outputs = &mut outputs_part[..input_size];
            assert!(outputs.len() * 4 == inputs.len());
            assert!(outputs.len().is_power_of_two());

            worker.scope(outputs.len(), |scope, chunk| {
                for (o, i) in outputs.chunks_mut(chunk)
                                .zip(inputs.chunks(chunk*4)) {
                    scope.spawn(move |_| {
                        for (o, i) in o.iter_mut().zip(i.chunks(4)) {
                            let mut hasher = PoseidonR4C1::new(params);
                            hasher.absorb(i[0]);
                            hasher.absorb(i[1]);
                            *o = hasher.squeeze();
                        }
                    });
                }
            });
        }

        Self {
            size: size,
            values_per_leaf: values_per_leaf,
            nodes: nodes,
            params: params,
            tree_type: TreeType::Tree4To1,
        }
    }

    fn create_2_to_1_tree(values: &[Params::Fr], size: usize, values_per_leaf: usize, params: &'a Params) -> Self {

        assert!(values_per_leaf.is_power_of_two());
        assert!(values.len() == size * values_per_leaf);

        let num_nodes = size;
        let mut nodes = vec![Params::Fr::zero(); num_nodes];

        let worker = Worker::new();
        let mut leaf_hashes = vec![Params::Fr::zero(); num_nodes];
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
                            *lh = Self::hash_into_leaf(&values[values_start..values_end], params, TreeType::Tree2To1);
                        }
                    });
                }
            });
        }

        // leafs are now encoded and hashed, so let's make a tree

        let mut num_levels = log2_floor(num_nodes) as usize;
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
            tree_type: TreeType::Tree2To1,
        }
    }
}

#[test]
fn test_poseidon_tree() {

    use std::time::{Duration, Instant};

    const SIZE: usize = 1048576;
    const VALUES_PER_LEAF: usize = 4;
    let params = Bn256_2_to_1_128s::new::<BlakeHasher>();
    
    let values : Vec<Fr> = (0..(SIZE * VALUES_PER_LEAF)).scan(Fr::multiplicative_generator(), |cur, _| {
        let res = cur.clone();
        cur.double();
        Some(res)
    }).collect();

    let now = Instant::now();
    let tree = PoseidonBN256Tree::create(&values[..], SIZE, VALUES_PER_LEAF, &params, TreeType::Tree2To1);

    println!("Poseidon MerkleTreeConstruction of size {} took {}s", SIZE, now.elapsed().as_secs());
}


#[test]
fn measure_poseidon_speed() {

    use std::time::{Duration, Instant};

    const SIZE: usize = 4194304;
    const VALUES_PER_LEAF : usize = 32;

    // measuring BN256
    let bn_values : Vec<Fr> = (0..(SIZE * VALUES_PER_LEAF)).scan(Fr::multiplicative_generator(), |cur, _| {
        let res = cur.clone();
        cur.double();
        Some(res)
    }).collect();

    {
        let params = Bn256_2_to_1_128s::new::<BlakeHasher>();
        let now = Instant::now();
        let tree = PoseidonBN256Tree::create(&bn_values[..], SIZE, VALUES_PER_LEAF, &params, TreeType::Tree2To1);

        println!("Poseidon_BN_256_2_1_128 MerkleTreeConstruction of size {} took {}s", SIZE, now.elapsed().as_secs());
    }

    {
        let params = Bn256_2_to_1_80s::new::<BlakeHasher>();
        let now = Instant::now();
        let tree = PoseidonBN256Tree::create(&bn_values[..], SIZE, VALUES_PER_LEAF, &params, TreeType::Tree2To1);

        println!("Poseidon_BN_256_2_1_80 MerkleTreeConstruction of size {} took {}s", SIZE, now.elapsed().as_secs());
    }

    {
        let params = Bn256_4_to_1_80s::new::<BlakeHasher>();
        let now = Instant::now();
        let tree = PoseidonBN256Tree::create(&bn_values[..], SIZE, VALUES_PER_LEAF, &params, TreeType::Tree4To1);

        println!("Poseidon_BN_256_4_1_80 MerkleTreeConstruction of size {} took {}s", SIZE, now.elapsed().as_secs());
    }

    let bls_values : Vec<<Bls12 as ScalarEngine>::Fr> = (0..(SIZE * VALUES_PER_LEAF)).scan(<Bls12 as ScalarEngine>::Fr::multiplicative_generator(), |cur, _| {
        let res = cur.clone();
        cur.double();
        Some(res)
    }).collect();

    {
        let params = BLS_2_to_1_80s::new::<BlakeHasher>();
        let now = Instant::now();
        let tree = PoseidonBN256Tree::create(&bls_values[..], SIZE, VALUES_PER_LEAF, &params, TreeType::Tree2To1);

        println!("Poseidon_BLS_2_1_80 MerkleTreeConstruction of size {} took {}s", SIZE, now.elapsed().as_secs());
    }

    {
        let params = BLS_4_to_1_80s::new::<BlakeHasher>();
        let now = Instant::now();
        let tree = PoseidonBN256Tree::create(&bls_values[..], SIZE, VALUES_PER_LEAF, &params, TreeType::Tree4To1);

        println!("Poseidon_BLS_4_1_80 MerkleTreeConstruction of size {} took {}s", SIZE, now.elapsed().as_secs());
    }

    let stark_values : Vec<StarkFr> = (0..(SIZE * VALUES_PER_LEAF)).scan(StarkFr::multiplicative_generator(), |cur, _| {
        let res = cur.clone();
        cur.double();
        Some(res)
    }).collect();

    {
        let params = Stark_2_to_1_80s::new::<BlakeHasher>();
        let now = Instant::now();
        let tree = PoseidonBN256Tree::create(&stark_values[..], SIZE, VALUES_PER_LEAF, &params, TreeType::Tree2To1);

        println!("Poseidon_Stark_2_1_80 MerkleTreeConstruction of size {} took {}s", SIZE, now.elapsed().as_secs());
    }

    {
        let params = Stark_4_to_1_80s::new::<BlakeHasher>();
        let now = Instant::now();
        let tree = PoseidonBN256Tree::create(&stark_values[..], SIZE, VALUES_PER_LEAF, &params, TreeType::Tree4To1);

        println!("Poseidon_Stark_4_1_80 MerkleTreeConstruction of size {} took {}s", SIZE, now.elapsed().as_secs());
    }

}




