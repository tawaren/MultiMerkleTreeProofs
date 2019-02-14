use std::fmt::Debug;

pub trait HashableNode {
    fn hash_merge(&self, other:Self) -> Self;
}

//Could be Optimized: If T had: genEmpty() & isEmpty() -- Then caller can use Option::None or 0x0000..0000 as empty
pub struct TreeHash<T>(Vec<Option<T>>);

impl<T:HashableNode+Clone+Debug> TreeHash<T> {

    pub fn new(root_level:usize) -> Self {
        //vec![None;root_level+1] would have been more elegant but requires that T implements clone
        let mut level_store = Vec::with_capacity(root_level+1);
        for _ in 0..(root_level+1) {level_store.push(None)}
        TreeHash(level_store)
    }

    //Normal tree hash would only expose a push_leaf(&mut self, leaf:T) {return self.push_node(0, leaf)}
    pub fn push_node(&mut self, level:usize, node:T) -> bool {
        if level >= self.0.len() {
            return false
        }

        self.0[level] = match &self.0[level] {
            None => Some(node),
            Some(existing) => {
                if !self.push_node( level+1, existing.hash_merge(node)) {
                    return false;
                }
                None
            },
        };

        true
    }

    //Normal tree hash would not need this
    pub fn push_left_nodes(&mut self, level_indicators:u64, nodes:&[T]) -> bool{
        let mut indicator = level_indicators;
        let mut level = 0;
        //init the precalced left nodes
        for node in nodes {
            //find the level of the next node for this side
            while indicator & 1 == 0 {
                level+=1;
                indicator >>= 1;
            }

            //process the node
            if !self.push_node(level, node.clone()){
                return false;
            }

            //up a level
            level+=1;
            indicator >>= 1;
        }
        true
    }

    pub fn push_right_nodes(&mut self, level_indicators:u64, nodes:&[T]) -> bool {
        self.push_left_nodes(!level_indicators,nodes)
    }

    pub fn finalize(mut self) -> Option<T> {
        //ensure that there were not to much or to less nodes in the proof
        for level in 0..(self.0.len()-1) {
            if self.0[level].is_some() {
                return None
            }
        }
        //return the the root hash
        self.0.pop().unwrap_or_default()
    }
}

