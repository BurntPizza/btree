

#[cfg(test)]
#[macro_use]
extern crate quickcheck as qc;

use std::mem;
use std::ops::DerefMut;
use std::ops::RangeFrom;
use std::iter::FromIterator;
use std::marker::PhantomData;
use std::collections::HashMap;


const LEAF_SIZE: usize = 64;
const DIR_SIZE: usize = 64;
const LEAF_BIN_SEARCH_THRESHOLD: usize = 0;
const DIR_BIN_SEARCH_THRESHOLD: usize = 0;
const BULK_LOAD_FACTOR: f64 = 1.0;

type Len = u16;
type NodeIdType = u32;


/// Immutable B+ tree
pub struct BTree<K, V, S> {
    root: NodeId,
    store: S,
    _marker: PhantomData<(K, V)>,
}

/// KV store for storing the nodes of BTrees
pub trait Store<K, V> {
    fn put(&mut self, node: Node<K, V>) -> NodeId;
    fn get(&self, node: NodeId) -> Option<&Node<K, V>>;
    fn get_mut(&mut self, node: NodeId) -> Option<&mut Node<K, V>>;
}

pub struct HeapStore<K, V> {
    map: HashMap<NodeId, Node<K, V>>,
}

impl<K, V> HeapStore<K, V> {
    pub fn new() -> Self {
        HeapStore { map: HashMap::new() }
    }

    fn next_id(&self) -> NodeId {
        NodeId::from(self.map.len() as NodeIdType)
    }
}

impl<K, V> Store<K, V> for HeapStore<K, V> {
    fn put(&mut self, node: Node<K, V>) -> NodeId {
        let id = self.next_id();
        self.map.insert(id, node);
        id
    }

    fn get(&self, node: NodeId) -> Option<&Node<K, V>> {
        self.map.get(&node)
    }

    fn get_mut(&mut self, node: NodeId) -> Option<&mut Node<K, V>> {
        self.map.get_mut(&node)
    }
}

impl<T, K, V> Store<K, V> for T
where
    T: DerefMut<Target = Store<K, V>>,
{
    fn put(&mut self, node: Node<K, V>) -> NodeId {
        self.deref_mut().put(node)
    }
    fn get(&self, node: NodeId) -> Option<&Node<K, V>> {
        self.deref().get(node)
    }
    fn get_mut(&mut self, node: NodeId) -> Option<&mut Node<K, V>> {
        self.deref_mut().get_mut(node)
    }
}

#[derive(Copy, Clone, PartialEq, Eq, Hash)]
pub struct NodeId(NodeIdType);

impl From<NodeIdType> for NodeId {
    fn from(x: NodeIdType) -> Self {
        NodeId(x)
    }
}

impl<K, V, S> BTree<K, V, S>
where
    S: Store<K, V>,
{
    pub fn new(mut store: S) -> Self {
        BTree {
            root: store.put(Node::leaf()),
            store,
            _marker: PhantomData,
        }
    }
}

impl<K, V, S> BTree<K, V, S>
where
    K: Ord,
    S: Store<K, V>,
{
    pub fn get(&self, key: &K) -> Option<&V> {
        self.get_leaf_idx(key).map(|(leaf, i)| &leaf.values[i])
    }

    pub fn insert_mut(&mut self, key: K, val: V) {
        let id = self.root;
        self.insert_into(id, key, val)
    }

    fn insert_into(&mut self, node: NodeId, key: K, val: V) {
        match self.store.get_mut(node) {
            Some(&mut Node::Leaf(ref mut leaf)) => {
                match leaf.key_position(&key) {
                    // key already exists
                    Ok(i) => unimplemented!(),

                    // key does not exist
                    // cases: i <  len && len < LEAF_SIZE  : insert
                    //        i == len && len < LEAF_SIZE  : insert
                    //        i <  len && len == LEAF_SIZE : split
                    //        i == len && len == LEAF_SIZE : split
                    Err(i) => {
                        debug_assert!(i <= leaf.len as usize);
                        if (leaf.len as usize) < LEAF_SIZE {
                            let ptr = leaf.keys.as_mut_ptr();
                            insert_into_slice(ptr, key, i, &mut leaf.len);
                        } else  {
                            // need to split
                            unimplemented!()
                        }
                    }
                }
            }
            Some(&mut Node::Dir(ref mut dir)) => {}
            _ => unreachable!(),
        }
    }

    pub fn range_from<R>(&self, range: R) -> RangeFromIter<K, V, S>
    where
        R: Into<RangeFrom<K>>,
    {
        let key = range.into().start;
        // If leaf is found...
        let node = self.find_leaf(&key, self.root).and_then(|node| {
            // and it contains the key
            node.key_position(&key).ok().map(|i| (node, i))
        });

        RangeFromIter {
            store: &self.store,
            node,
        }
    }

    fn get_leaf_idx(&self, key: &K) -> Option<(&Leaf<K, V>, usize)> {
        self.find_leaf(key, self.root).and_then(|leaf| {
            leaf.key_position(key).ok().map(|i| (leaf, i))
        })
    }

    fn find_leaf(&self, key: &K, start_node: NodeId) -> Option<&Leaf<K, V>> {
        self.store.get(start_node).and_then(|node| match *node {
            Node::Leaf(ref leaf) => Some(leaf.clone()),
            Node::Dir(ref dir) => {
                dir.key_position(key).and_then(|i| {
                    self.find_leaf(key, dir.children[i])
                })
            }
        })
    }
}

// impl<K, V> FromIterator<(K, V)> for BTree<K, V, HeapStore<K, V>>
// where
//     K: Ord,
// {
//     fn from_iter<T>(iter: T) -> Self
//     where
//         T: IntoIterator<Item = (K, V)>,
//     {
//         let mut records: Vec<_> = iter.into_iter().collect();
//         let pre_len = records.len();

//         records.sort_by_key(|&(k, _)| k);
//         records.dedup_by_key(|&mut (k, _)| k);

//         if records.len() != pre_len {
//             panic!("Duplicate keys");
//         }

//         let mut store = HeapStore::new();

//         match records.len() {
//             0 => BTree::new(store),
//             n if n <= LEAF_SIZE => {
//                 let mut leaf = Leaf::uninitialized();

//                 for (i, (k, v)) in records.into_iter().enumerate() {
//                     leaf.keys[i] = k;
//                     leaf.values[i] = v;
//                     leaf.len += 1;
//                 }

//                 let root_id = store.put(Node::Leaf(leaf));

//                 BTree {
//                     root: root_id,
//                     store: store,
//                     _marker: PhantomData,
//                 }
//             }
//             n => {
//                 let mut records = records.into_iter();
//                 let num_leaves = n / LEAF_SIZE;
//                 let last_leaf_len = n % LEAF_SIZE;


//                 loop {

//                     let mut leaf = Leaf::uninitialized();
//                     let mut i = 0;

//                     while let Some((k, v)) = records.next() {
//                         leaf.keys[i] = k;
//                         leaf.values[i] = v;
//                         leaf.len += 1;
//                         i += 1;

//                         if i == LEAF_SIZE {
//                             break;
//                         }
//                     }

//                     let id = store.put(Node::Leaf(leaf));

//                 }
//             }
//         }
//     }
// }

pub struct RangeFromIter<'a, K: 'a, V: 'a, S: 'a> {
    store: &'a S,
    node: Option<(&'a Leaf<K, V>, usize)>,
}

impl<'a, K, V, S> Iterator for RangeFromIter<'a, K, V, S>
where
    S: Store<K, V>,
{
    type Item = &'a V;

    fn next(&mut self) -> Option<Self::Item> {
        self.node.map(|(ref node, ref mut idx)| {
            debug_assert!(*idx < node.len as usize);
            let value = &node.values[*idx];
            *idx += 1;

            if *idx >= node.len as usize {
                self.node = node.next.and_then(|id| {
                    self.store.get(id).map(|node| match *node {
                        Node::Leaf(ref leaf) => {
                            debug_assert!(leaf.len > 0);
                            (leaf, 0)
                        }
                        _ => unreachable!(),
                    })
                });
            }

            value
        })
    }
}

pub enum Node<K, V> {
    Leaf(Leaf<K, V>),
    Dir(Dir<K>),
}

impl<K, V> Node<K, V> {
    fn leaf() -> Self {
        Node::Leaf(Leaf::uninitialized())
    }
}

pub struct Leaf<K, V> {
    keys: [K; LEAF_SIZE],
    values: [V; LEAF_SIZE],
    next: Option<NodeId>,
    len: Len,
}

impl<K, V> Leaf<K, V> {
    fn uninitialized() -> Self {
        unsafe {
            Leaf {
                keys: mem::uninitialized(),
                values: mem::uninitialized(),
                next: None,
                len: 0,
            }
        }
    }
}

impl<K, V> Leaf<K, V>
where
    K: Ord,
{
    fn key_position(&self, key: &K) -> Result<usize, usize> {
        debug_assert!((self.len as usize) <= LEAF_SIZE);
        let keys = &self.keys[..self.len as usize];

        if LEAF_SIZE < LEAF_BIN_SEARCH_THRESHOLD {
            linear_search(&self.keys, key)
        } else {
            keys.binary_search(key)
        }
    }
}

pub struct Dir<K> {
    keys: [K; DIR_SIZE - 1],
    children: [NodeId; DIR_SIZE],
    len: Len,
}

impl<K> Dir<K>
where
    K: Ord,
{
    fn key_position(&self, key: &K) -> Option<usize> {
        debug_assert!((self.len as usize) < self.keys.len());
        let keys = &self.keys[..self.len as usize];

        if DIR_SIZE < DIR_BIN_SEARCH_THRESHOLD {
            keys.iter().position(|k| k >= key)
        } else {
            keys.binary_search(key).ok()
        }
    }
}

fn linear_search<T: Ord>(slice: &[T], key: &T) -> Result<usize, usize> {
    use std::cmp::Ordering;

    for i in 0..slice.len() {
        match slice[i].cmp(key) {
            Ordering::Greater => return Err(i),
            Ordering::Equal => return Ok(i),
            _ => {}
        }
    }

    Err(slice.len())
}

// ptr must point to memory valid for len + 1 elements
fn insert_into_slice<T>(ptr: *mut T, val: T, i: usize, len: &mut Len) {
    unsafe {
        // shift elements over
        let n = *len as usize - i;
        std::ptr::copy(ptr.offset(i as isize), ptr.offset(i as isize + 1), n);
        // insert into gap
        std::ptr::write(ptr.offset(i as isize), val);
    }

    // inc length
    *len += 1;
}

#[cfg(test)]
mod tests {
    use super::*;

    quickcheck! {
        fn searches_equal(xs: Vec<u32>, key: u32) -> bool {
            let mut xs = xs;
            xs.sort();
            xs.dedup();
            linear_search(&*xs, &key) == xs.binary_search(&key)
        }

        fn insert_slice(xs: Vec<u32>, val: u32, i: usize) -> qc::TestResult {
            if i >= xs.len() {
                return qc::TestResult::discard();
            }

            let mut xs = xs;
            let mut copy = xs.clone();
            copy.insert(i, val);
            let mut len = xs.len() as Len;

            xs.reserve(1);
            insert_into_slice(xs.as_mut_ptr(), val, i, &mut len);
            unsafe { xs.set_len(len as usize); }

            qc::TestResult::from_bool(xs == copy)
        }
    }
}
