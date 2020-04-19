use crate::pairing::{Engine};
use crate::pairing::ff::{PrimeField, PrimeFieldRepr};
use crate::multicore::Worker;
use crate::plonk::commitments::transparent::utils::log2_floor;
use super::*;
use super::tree_hash::*;

#[derive(Debug)]
pub struct BinaryTree<E: Engine, H: BinaryTreeHasher<E::Fr>> {
    size: usize,
    nodes: Vec<H::Output>,
    params: BinaryTreeParams,
    tree_hasher: H,
    _marker: std::marker::PhantomData<E>
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct BinaryTreeParams {
    pub values_per_leaf: usize
}

use std::time::Instant;

impl<E: Engine, H: BinaryTreeHasher<E::Fr>> BinaryTree<E, H> {
    fn hash_into_leaf(tree_hasher: &H, values: &[E::Fr]) -> H::Output {
        tree_hasher.leaf_hash(values)
    }

    fn make_full_path(&self, leaf_index: usize, leaf_pair_hash: H::Output) -> Vec<H::Output> {
        let mut nodes = &self.nodes[..];

        let mut path = vec![];
        path.push(leaf_pair_hash);

        let mut idx = leaf_index;
        idx >>= 1;

        for _ in 0..log2_floor(nodes.len() / 2) {
            let half_len = nodes.len() / 2;
            let (next_level, this_level) = nodes.split_at(half_len);
            let pair_idx = idx ^ 1usize;
            let value = this_level[pair_idx];
            path.push(value);
            idx >>= 1;
            nodes = next_level;
        }

        path
    }

    pub(crate) fn size(&self) -> usize {
        self.size
    }

    pub(crate) fn create_from_combined_leafs(leafs: &[Vec<&[E::Fr]>], tree_hasher: H, params: &BinaryTreeParams) -> Self {
        let values_per_leaf = params.values_per_leaf;
        let num_leafs = leafs.len();
        let values_per_leaf_supplied = leafs[0].len() * leafs[0][0].len();
        assert!(values_per_leaf == values_per_leaf_supplied);
        assert!(num_leafs.is_power_of_two());

        let num_nodes = num_leafs;

        let size = num_leafs;

        let mut nodes = vec![H::placeholder_output(); num_nodes];

        let worker = Worker::new();

        let mut leaf_hashes = vec![H::placeholder_output(); num_leafs];

        let hasher_ref = &tree_hasher;

        {
            worker.scope(leaf_hashes.len(), |scope, chunk| {
                for (i, lh) in leaf_hashes.chunks_mut(chunk)
                                .enumerate() {
                    scope.spawn(move |_| {
                        let mut scratch_space = Vec::with_capacity(values_per_leaf);
                        let base_idx = i*chunk;
                        for (j, lh) in lh.iter_mut().enumerate() {
                            let idx = base_idx + j;
                            let leaf_values_ref = &leafs[idx];
                            for &lv in leaf_values_ref.iter() {
                                scratch_space.extend_from_slice(lv);
                            }
                            *lh = hasher_ref.leaf_hash(&scratch_space[..]);
                            scratch_space.truncate(0);
                        }
                    });
                }
            });
        }

        // leafs are now encoded and hashed, so let's make a tree

        let num_levels = log2_floor(num_leafs) as usize;
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
                        let mut hash_input = [H::placeholder_output(); 2];
                        for (o, i) in o.iter_mut().zip(i.chunks(2)) {
                            hash_input[0] = i[0];
                            hash_input[1] = i[1];
                            *o = hasher_ref.node_hash(&hash_input, _level);
                        }
                    });
                }
            });
        }

        for _level in (0..(num_levels-1)).rev() {
            // do the trick - split
            let (next_levels, inputs) = nodes_for_hashing.split_at_mut(nodes_for_hashing.len()/2);
            let (_, outputs) = next_levels.split_at_mut(next_levels.len() / 2);
            assert!(outputs.len() * 2 == inputs.len());
            assert!(outputs.len().is_power_of_two());

            worker.scope(outputs.len(), |scope, chunk| {
                for (o, i) in outputs.chunks_mut(chunk)
                                .zip(inputs.chunks(chunk*2)) {
                    scope.spawn(move |_| {
                        let mut hash_input = [H::placeholder_output(); 2];
                        for (o, i) in o.iter_mut().zip(i.chunks(2)) {
                            hash_input[0] = i[0];
                            hash_input[1] = i[1];
                            *o = hasher_ref.node_hash(&hash_input, _level);
                        }
                    });
                }
            });

            nodes_for_hashing = next_levels;
        }

        Self {
            size: size,
            nodes: nodes,
            tree_hasher: tree_hasher,
            params: params.clone(),
            _marker: std::marker::PhantomData
        }

    }

    pub(crate) fn create(values: &[E::Fr], tree_hasher: H, params: &BinaryTreeParams) -> Self {
        assert!(params.values_per_leaf.is_power_of_two());

        let values_per_leaf = params.values_per_leaf;
        let num_leafs = values.len() / values_per_leaf;
        assert!(num_leafs.is_power_of_two());

        let num_nodes = num_leafs;

        let size = num_leafs;

        let mut nodes = vec![H::placeholder_output(); num_nodes];

        let worker = Worker::new();

        let mut leaf_hashes = vec![H::placeholder_output(); num_leafs];

        let hasher_ref = &tree_hasher;

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
                            *lh = hasher_ref.leaf_hash(&values[values_start..values_end]);
                        }
                    });
                }
            });
        }

        // leafs are now encoded and hashed, so let's make a tree

        let num_levels = log2_floor(num_leafs) as usize;
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
                        let mut hash_input = [H::placeholder_output(); 2];
                        for (o, i) in o.iter_mut().zip(i.chunks(2)) {
                            hash_input[0] = i[0];
                            hash_input[1] = i[1];
                            *o = hasher_ref.node_hash(&hash_input, _level);
                        }
                    });
                }
            });
        }

        for _level in (0..(num_levels-1)).rev() {
            // do the trick - split
            let (next_levels, inputs) = nodes_for_hashing.split_at_mut(nodes_for_hashing.len()/2);
            let (_, outputs) = next_levels.split_at_mut(next_levels.len() / 2);
            assert!(outputs.len() * 2 == inputs.len());
            assert!(outputs.len().is_power_of_two());

            worker.scope(outputs.len(), |scope, chunk| {
                for (o, i) in outputs.chunks_mut(chunk)
                                .zip(inputs.chunks(chunk*2)) {
                    scope.spawn(move |_| {
                        let mut hash_input = [H::placeholder_output(); 2];
                        for (o, i) in o.iter_mut().zip(i.chunks(2)) {
                            hash_input[0] = i[0];
                            hash_input[1] = i[1];
                            *o = hasher_ref.node_hash(&hash_input, _level);
                        }
                    });
                }
            });

            nodes_for_hashing = next_levels;
        }

        Self {
            size: size,
            nodes: nodes,
            tree_hasher: tree_hasher,
            params: params.clone(),
            _marker: std::marker::PhantomData
        }
    }

    fn get_commitment(&self) -> H::Output {
        self.nodes[1].clone()
    }

    fn produce_query(&self, indexes: Vec<usize>, values: &[E::Fr]) -> Query<E, H> {
        // we never expect that query is mis-alligned, so check it
        debug_assert!(indexes[0] % self.params.values_per_leaf == 0);
        debug_assert!(indexes.len() == self.params.values_per_leaf);
        debug_assert!(indexes == (indexes[0]..(indexes[0]+self.params.values_per_leaf)).collect::<Vec<_>>());
        debug_assert!(*indexes.last().expect("is some") < self.size());
        debug_assert!(*indexes.last().expect("is some") < values.len());

        let query_values = Vec::from(&values[indexes[0]..(indexes[0]+self.params.values_per_leaf)]);

        let leaf_index = indexes[0] / self.params.values_per_leaf;

        let pair_index = leaf_index ^ 1;

        let leaf_pair_hash = self.tree_hasher.leaf_hash(&values[(pair_index*self.params.values_per_leaf)..((pair_index+1)*self.params.values_per_leaf)]);

        let path = self.make_full_path(leaf_index, leaf_pair_hash);

        Query::<E, H> {
            indexes: indexes,
            values: query_values,
            path: path,
        }
    }

    fn verify_query(
        commitment: &H::Output, 
        query: &Query<E, H>, 
        params: &BinaryTreeParams, 
        tree_hasher: &H
    ) -> bool {
        if query.values().len() != params.values_per_leaf {
            return false;
        }

        let mut hash = tree_hasher.leaf_hash(query.values());
        let mut idx = query.indexes()[0] / params.values_per_leaf;
        let mut hash_input = [H::placeholder_output(); 2];

        for el in query.path.iter() {
            {
                if idx & 1usize == 0 {
                    hash_input[0] = hash;
                    hash_input[1] = *el;
                } else {
                    hash_input[0] = *el;
                    hash_input[1] = hash;
                }
            }
            hash = tree_hasher.node_hash(&hash_input, 0);
            idx >>= 1;
        }

        &hash == commitment
    }
}

impl<E: Engine, H: BinaryTreeHasher<E::Fr>> PartialEq for BinaryTree<E, H> {
    fn eq(&self, other: &Self) -> bool {
        self.get_commitment() == other.get_commitment()
    }
}

impl<E: Engine, H: BinaryTreeHasher<E::Fr>> Eq for BinaryTree<E, H> {}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Query<E: Engine, H: BinaryTreeHasher<E::Fr>> {
    indexes: Vec<usize>,
    values: Vec<E::Fr>,
    path: Vec<H::Output>,
}

impl<E: Engine, H: BinaryTreeHasher<E::Fr>> Query<E, H> {
    fn indexes(&self) -> Vec<usize> {
        self.indexes.clone()
    }

    fn values(&self) -> &[E::Fr] {
        &self.values
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::ff::Field;
    use crate::pairing::bn256::{Bn256, Fr};
    use rescue_hash::bn256::Bn256RescueParams;

    // const SIZE: usize = 16;
    // const VALUES_PER_LEAF: usize = 4;
    const SIZE: usize = 24;
    const VALUES_PER_LEAF: usize = 8;

    #[test]
    fn make_binary_tree() {
        let mut inputs = vec![];
        let mut f = Fr::one();
        for _ in 0..SIZE {
            inputs.push(f);
            f.double();
        }

        let params = Bn256RescueParams::new_checked_2_into_1();
        let hasher = RescueBinaryTreeHasher::new(&params);

        let tree_params = BinaryTreeParams {
            values_per_leaf: VALUES_PER_LEAF
        };

        let iop = BinaryTree::create(&inputs, hasher.clone(), &tree_params);
        let commitment = iop.get_commitment();
        let tree_size = iop.size();
        assert!(tree_size == SIZE);
        assert!(iop.nodes.len() == (SIZE / VALUES_PER_LEAF));
        for i in 0..(SIZE / VALUES_PER_LEAF) {
            let indexes: Vec<_> = ((i*VALUES_PER_LEAF)..(VALUES_PER_LEAF + i*VALUES_PER_LEAF)).collect();
            let query = iop.produce_query(indexes, &inputs);
            let valid = BinaryTree::<Bn256, RescueBinaryTreeHasher<Bn256>>::verify_query(
                &commitment, 
                &query, 
                &tree_params,
                &hasher
            );
            assert!(valid, "invalid query for leaf index {}", i);
        }
    }
}