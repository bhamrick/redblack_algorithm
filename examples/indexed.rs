//! This example creates a balanced index tree, allowing for arbitrary placement inserts
//! and lookups in O(log n) time.

use std::cmp::Ordering;

use redblack_algorithm::*;

// Nodes in an indexed tree also contain the size of their subtree.
#[derive(Debug)]
struct Node {
    size: usize,
    value: i32,
    left: Option<(Box<Node>, Color)>,
    right: Option<(Box<Node>, Color)>,
}

impl PackContext<i32, Box<Node>> for () {
    fn unpack(&mut self, node: Box<Node>) -> RedBlackData<i32, Box<Node>> {
        RedBlackData {
            data: node.value,
            left: node.left,
            right: node.right,
        }
    }

    // `pack` computes the size of the subtree created when putting it together.
    fn pack(&mut self, data: RedBlackData<i32, Box<Node>>) -> Box<Node> {
        let left_size = match &data.left {
            Some((n, _)) => n.size,
            None => 0,
        };
        let right_size = match &data.right {
            Some((n, _)) => n.size,
            None => 0,
        };
        Box::new(Node {
            size: left_size + right_size + 1,
            value: data.data,
            left: data.left,
            right: data.right,
        })
    }
}

#[derive(Debug)]
struct IndexedTree {
    root: Option<Box<Node>>,
}

impl IndexedTree {
    fn new() -> IndexedTree {
        IndexedTree { root: None }
    }

    fn insert(&mut self, index: usize, value: i32) {
        self.root = Some(insert(
            self.root.take(),
            &mut |node: &RedBlackData<i32, Box<Node>>, i: Option<usize>| {
                let i = i.unwrap_or(index);
                let left_size = match &node.left {
                    Some((n, _)) => n.size,
                    None => 0,
                };
                match i.cmp(&left_size) {
                    Ordering::Less | Ordering::Equal => Some((Direction::Left, i)),
                    Ordering::Greater => Some((Direction::Right, i - left_size - 1)),
                }
            },
            value,
            &mut (),
        ));
    }

    fn delete(&mut self, index: usize) {
        self.root = delete(
            self.root.take(),
            &mut |node: &RedBlackData<i32, Box<Node>>, i: Option<usize>| {
                let i = i.unwrap_or(index);
                let left_size = match &node.left {
                    Some((n, _)) => n.size,
                    None => 0,
                };
                match i.cmp(&left_size) {
                    Ordering::Less => Some((Direction::Left, i)),
                    Ordering::Equal => None,
                    Ordering::Greater => Some((Direction::Right, i - left_size - 1)),
                }
            },
            &mut (),
        );
    }

    fn get(&self, index: usize) -> Option<i32> {
        let mut focus = self.root.as_ref();
        let mut i = index;
        while let Some(n) = focus {
            let left_size = match &n.left {
                Some((n, _)) => n.size,
                None => 0,
            };
            match i.cmp(&left_size) {
                Ordering::Less => {
                    focus = match n.left {
                        Some((ref child, _)) => Some(child),
                        None => None,
                    };
                }
                Ordering::Equal => return Some(n.value),
                Ordering::Greater => {
                    i = i - left_size - 1;
                    focus = match n.right {
                        Some((ref child, _)) => Some(child),
                        None => None,
                    };
                }
            }
        }
        None
    }
}

fn main() {
    let mut tree = IndexedTree::new();
    for i in 1..10 {
        tree.insert(0, i);
    }
    tree.delete(3);
    tree.insert(4, 0);
    println!("{:?}", tree);
    for i in 0..9 {
        println!("{} {:?}", i, tree.get(i));
    }
}
