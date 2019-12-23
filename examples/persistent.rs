#![allow(unused_variables)]
#![allow(unused_imports)]
#![allow(dead_code)]
use std::cmp::Ordering;

use redblack_algorithm::*;

#[derive(Debug)]
struct Node {
    key: i32,
    left: (Option<usize>, Color),
    right: (Option<usize>, Color),
}

#[derive(Debug)]
struct PersistentTree {
    nodes: Vec<Node>,
}

impl PackContext<i32, usize> for PersistentTree {
    fn unpack(&mut self, index: usize) -> RedBlackData<i32, usize> {
        let n = &self.nodes[index];
        RedBlackData {
            data: n.key,
            left: n.left,
            right: n.right,
        }
    }

    fn pack(&mut self, data: RedBlackData<i32, usize>) -> usize {
        self.nodes.push(Node {
            key: data.data,
            left: data.left,
            right: data.right,
        });
        self.nodes.len() - 1
    }
}

impl PersistentTree {
    fn new() -> PersistentTree {
        PersistentTree { nodes: Vec::new() }
    }

    fn insert(&mut self, root: Option<usize>, value: i32) -> usize {
        let mut locate = |node: &RedBlackData<i32, usize>, _| match value.cmp(&node.data) {
            Ordering::Less => Some((Direction::Left, ())),
            Ordering::Equal => None,
            Ordering::Greater => Some((Direction::Right, ())),
        };
        insert(root, &mut locate, value, self)
    }

    fn remove(&mut self, root: Option<usize>, value: i32) -> Option<usize> {
        let mut locate = |node: &RedBlackData<i32, usize>, _| match value.cmp(&node.data) {
            Ordering::Less => Some((Direction::Left, ())),
            Ordering::Equal => None,
            Ordering::Greater => Some((Direction::Right, ())),
        };
        delete(root, &mut locate, self)
    }
}

fn main() {
    let mut tree = PersistentTree::new();
    let mut roots = Vec::new();
    roots.push(None);
    let mut root = None;
    for i in 1..10 {
        let new_root = Some(tree.insert(root, i));
        roots.push(new_root);
        root = new_root;
    }
    for i in 1..10 {
        let new_root = tree.remove(root, i);
        roots.push(new_root);
        root = new_root;
    }
    for (i, n) in tree.nodes.iter().enumerate() {
        println!("{}: {:?}", i, n);
    }
    println!("{:?}", roots);
}
