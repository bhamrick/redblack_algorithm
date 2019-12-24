//! This example creates a basic binary search tree using Box for parent-child links.

use std::cmp::Ordering;

use redblack_algorithm::*;

#[derive(Debug)]
struct Node {
    key: i32,
    left: Option<(Box<Node>, Color)>,
    right: Option<(Box<Node>, Color)>,
}

// No special context is required to convert between Box<Node> and RedBlackData<i32, Box<Node>>.
impl PackContext<i32, Box<Node>> for () {
    fn unpack(&mut self, node: Box<Node>) -> RedBlackData<i32, Box<Node>> {
        RedBlackData {
            data: node.key,
            left: node.left,
            right: node.right,
        }
    }

    fn pack(&mut self, data: RedBlackData<i32, Box<Node>>) -> Box<Node> {
        Box::new(Node {
            key: data.data,
            left: data.left,
            right: data.right,
        })
    }
}

#[derive(Debug)]
struct Tree {
    root: Option<Box<Node>>,
}

impl Tree {
    fn new() -> Tree {
        Tree {
            root: None,
        }
    }

    fn insert(&mut self, x: i32) {
        self.root = Some(insert(
            self.root.take(),
            &mut |node: &RedBlackData<i32, Box<Node>>, _| match x.cmp(&node.data) {
                Ordering::Less => Some((Direction::Left, ())),
                Ordering::Equal => None,
                Ordering::Greater => Some((Direction::Right, ())),
            },
            x,
            &mut (),
        ));
    }

    fn remove(&mut self, x: i32) {
        self.root = delete(
            self.root.take(),
            &mut |node: &RedBlackData<i32, Box<Node>>, _| match x.cmp(&node.data) {
                Ordering::Less => Some((Direction::Left, ())),
                Ordering::Equal => None,
                Ordering::Greater => Some((Direction::Right, ())),
            },
            &mut (),
        );
    }
}

fn main() {
    let mut tree = Tree::new();
    for i in 1..10 {
        tree.insert(i);
    }
    println!("{:?}", tree);
    tree.remove(4);
    println!("{:?}", tree);
}
