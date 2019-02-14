#[cfg(test)]
extern crate rand;

mod tree_hash;
mod path_utils;

use rand::prelude::*;
use std::fmt::Debug;
use crate::tree_hash::*;
use crate::path_utils::*;

#[derive(Debug)]
pub struct UnCompressedProof<T> {
    pub auth_path: Vec<T>,
    pub index:u64,
}

#[derive(Debug)]
pub struct CompressedProofs<T> {
    pub indices:Vec<u64>,
    pub tree_nodes: Vec<T>
}

//this soe extra memory for sorting
pub fn compress_unsorted_proofs<T:Clone>(mut proofs:Vec<UnCompressedProof<T>>) -> CompressedProofs<T> {
    let unsorted_indicies = proofs.iter().map(|p|p.index).collect();
    proofs.sort_by(|a, b| a.index.cmp(&b.index));
    let proof = compress_proofs(proofs);
    CompressedProofs {
        indices: unsorted_indicies,
        tree_nodes: proof.tree_nodes
    }
}
//Note: requires that no 2 proofs have same index
//todo: make a version accessing the tree directly eliminating the memory need for the auth paths
pub fn compress_proofs<T:Clone>(proofs:Vec<UnCompressedProof<T>>) -> CompressedProofs<T> {
    let mut tree_nodes = Vec::new();
    let mut indices = Vec::with_capacity(proofs.len());
    for (pos,UnCompressedProof{index,auth_path}) in proofs.iter().enumerate() {
        //the height of the tree
        let height = auth_path.len() as u32;
        //top levels covered by leading index - Note: the +1 is their as the first node after the paths diverge must not be emitted as it is computed
        let leading_trim = if pos > 0 {calc_unshared_path_len(proofs[pos-1].index, *index)} else {height};
        //top levels covered by trailing index - Note: the +1 is their as the first node after the paths diverge must not be emitted as it is computed
        let trailing_trim = if pos < (proofs.len()-1) {calc_unshared_path_len(proofs[pos+1].index, *index)} else {height};
        //trim and order the proof nodes (in traversal order for tree hash to consume when validating)
        //the leading nodes first
        tree_nodes.extend(
            auth_path.iter().enumerate()
                //keep the trailing that are not covered by an earlier path
                .filter(|(level,n)|has_left_sibling_on_level(*index, *level) && *level < leading_trim as usize)
                .map(|(_,n)|n.clone())
        );
        //the trailing nodes after
        tree_nodes.extend(
            auth_path.iter().enumerate()
                //keep the trailing that are not covered by a later path
                .filter(|(level,n)|has_right_sibling_on_level(*index, *level) && *level < trailing_trim as usize)
                .map(|(_,n)|n.clone())
        );
        //push the index
        indices.push(*index)
    }

    CompressedProofs {
        indices,
        tree_nodes
    }
}

//this function is using extra memory so already sorted representations should be preferred
//this function is not optimized and could be improved
pub fn calc_root_from_unsorted_proof<T:HashableNode+Clone+Debug>(expected_height:u32, values:&[T], CompressedProofs {indices,tree_nodes}: CompressedProofs<T>) -> Option<T>{
    let mut sorted:Vec<_> = indices.into_iter().zip(values.into_iter()).collect();
    sorted.sort_by(|a,b|a.0.cmp(&b.0));
    let values:Vec<_> = sorted.iter().map(|(i,v)|(*v).clone()).collect();
    let indices:Vec<_> = sorted.iter().map(|(i,v)|*i).collect();
    let proof = CompressedProofs {
        indices,
        tree_nodes
    };
    return calc_root_from_proof(expected_height,values,proof);
}

//This is the memory optimal part
pub fn calc_root_from_proof<T:HashableNode+Clone>(expected_height:u32, values:Vec<T>, CompressedProofs {indices,tree_nodes}: CompressedProofs<T>) -> Option<T> {
    assert_eq!(values.len(), indices.len());
    assert_ne!(values.len(), 0);

    let mut tree_hash = TreeHash::new(expected_height as usize);
    let mut progress = 0;
    for (pos,(index, value)) in  indices.iter().zip(values.into_iter()).enumerate() {
        //calculate the lengths
        let leading_len = if pos > 0 {calc_num_unshared_leading_elems(*index, indices[pos-1])} else {index.count_ones()} as usize;
        let trailing_len = if pos < (indices.len()-1) {calc_num_unshared_trailing_elems(*index, indices[pos+1])} else {expected_height - index.count_ones()} as usize;

        //compute the slice boundaries
        //do we have enough elems ?
        if progress+leading_len+trailing_len > tree_nodes.len() {return None}

        //get the leading
        let leading = &tree_nodes[progress..(progress+leading_len)];
        progress += leading_len;

        //get the trailing
        let trailing = &tree_nodes[progress..(progress+trailing_len)];
        progress += trailing_len;


        //Apply the tree hash
        if !tree_hash.push_left_nodes(*index, leading) {return None}
        if !tree_hash.push_node(0, value){return None}
        if !tree_hash.push_right_nodes(*index, trailing){return None}
    }

    //ensure that there were not to much or to less nodes in the proof
    tree_hash.finalize()
}


#[cfg(test)]
mod test {
    use super::*;
    use std::collections::BTreeSet;

    //Functions operating on a virtual tree
    #[derive(Ord, PartialOrd, Eq, PartialEq, Copy, Clone, Debug)]
    struct IndexVirtHash(u64);
    impl HashableNode for IndexVirtHash {
        fn hash_merge(&self, other: Self) -> Self {
            assert_eq!(self.0+1, other.0);
            IndexVirtHash(self.0 >> 1)
        }
    }

    fn leaf_index(index:u64, height:u64) -> u64 {
        index + (1 << height)
    }

    fn leaf_hash(index:u64, height:u64) -> IndexVirtHash {
        IndexVirtHash(leaf_index(index,height))
    }

    fn root_hash(height:u64) -> IndexVirtHash {
        IndexVirtHash(1)
    }

    fn virt_auth_for_index(index:u64, height:u64) -> Vec<IndexVirtHash> {
        let leaf_index = leaf_index(index,height);
        let mut auth = Vec::with_capacity(height as usize);
        for l in 0..height {
            auth.push(IndexVirtHash((leaf_index >> l)^1))
        }
        auth
    }

    const NUM_RAND_TRIES:u64 = 100000;
    const NUM_MAX_HEIGHT:u64 = 32;          //averages to 2^28 Leafes
    const NUM_MAX_ELEM:u64 = 128;           //averages to 64 Leafes

    #[test]
    fn test_single_same_elem() {
        let mut rng = rand::thread_rng();
        for _ in 0..NUM_RAND_TRIES {
            let height = (rng.gen_range(0u64,NUM_MAX_HEIGHT)+1) as u64;
            let index =  rng.gen_range(0u64,1u64 << height);
            let auth_path = virt_auth_for_index(index,height);
            let val = leaf_hash(index,height);
            let comp_auth = compress_proofs(vec![UnCompressedProof { auth_path:auth_path.clone(), index}]);
            assert_eq!(comp_auth.tree_nodes.len(), height as usize);
            assert_eq!(comp_auth.indices.len(), 1);

            for a in auth_path {
                assert!(comp_auth.tree_nodes.contains(&a))
            }

        }
    }

    #[test]
    fn test_left_most() {
        let mut rng = rand::thread_rng();
        for _ in 0..NUM_RAND_TRIES {
            let height = (rng.gen_range(0u64,NUM_MAX_HEIGHT)+1) as u64;
            let index =  0;
            let val = leaf_hash(index,height);
            let auth_path = virt_auth_for_index(index,height);
            let comp_auth = compress_proofs(vec![UnCompressedProof { auth_path:auth_path.clone(), index}]);
            assert_eq!(auth_path, comp_auth.tree_nodes);
            let res = calc_root_from_proof(height as u32,vec![val], comp_auth);
            assert_eq!(res,Some(root_hash(height)));
        }
    }

    #[test]
    fn test_right_most() {
        let mut rng = rand::thread_rng();
        for _ in 0..NUM_RAND_TRIES {
            let height = (rng.gen_range(0u64,NUM_MAX_HEIGHT)+1) as u64;
            let index =  (1 << height)-1;
            let val = leaf_hash(index,height);
            let auth_path = virt_auth_for_index(index,height);
            let comp_auth = compress_proofs(vec![UnCompressedProof { auth_path:auth_path.clone(), index}]);
            assert_eq!(auth_path, comp_auth.tree_nodes);
            let res = calc_root_from_proof(height as u32,vec![val], comp_auth);
            assert_eq!(res,Some(root_hash(height)));
        }
    }


    #[test]
    fn test_many() {
        let mut rng = rand::thread_rng();
        for _ in 0..NUM_RAND_TRIES {
            let height = (rng.gen_range(0u64,NUM_MAX_HEIGHT)+1) as u64;
            let amount = rng.gen_range(1u64,(NUM_MAX_ELEM+1).min(1u64 << height));
            let mut indexes = BTreeSet::new();
            for _ in 0..amount {
                indexes.insert(rng.gen_range(0u64,1u64 << height));
            }
            let mut auths = Vec::with_capacity(indexes.len());
            let mut vals = Vec::with_capacity(indexes.len());
            for index in indexes {
                let auth_path = virt_auth_for_index(index,height);
                auths.push(UnCompressedProof { auth_path, index});
                vals.push(leaf_hash(index,height));
            }
            let comp_auth = compress_proofs(auths);
            let res = calc_root_from_proof(height as u32,vals, comp_auth);
            assert_eq!(res,Some(root_hash(height)));
        }
    }


    #[test]
    fn test_single() {
        let mut rng = rand::thread_rng();
        for _ in 0..NUM_RAND_TRIES {
            let height = (rng.gen_range(0u64,NUM_MAX_HEIGHT)+1) as u64;
            let index =  rng.gen_range(0u64,1u64 << height);
            let auth_path = virt_auth_for_index(index,height);
            let val = leaf_hash(index,height);
            let comp_auth = compress_proofs(vec![UnCompressedProof { auth_path:auth_path.clone(), index}]);
            let res = calc_root_from_proof(height as u32,vec![val], comp_auth);
            assert_eq!(res,Some(root_hash(height)));
        }
    }
}