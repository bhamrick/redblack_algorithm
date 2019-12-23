#![allow(unused_variables)]
#![allow(unused_imports)]
#![allow(dead_code)]
use std::cmp::Ordering;

use redblack_algorithm::*;

#[derive(Debug)]
struct Object {
    data: (),
    rb_key: i32,
    rb_left: (Option<usize>, Color),
    rb_right: (Option<usize>, Color),
}

struct RbTree<'a>(&'a mut Vec<Object>);

struct ObjectData {
    index: usize,
    key: i32,
}

impl<'a> PackContext<ObjectData, usize> for RbTree<'a> {
    fn unpack(&mut self, index: usize) -> RedBlackData<ObjectData, usize> {
        let obj = &self.0[index];
        RedBlackData {
            data: ObjectData {
                index,
                key: obj.rb_key,
            },
            left: obj.rb_left,
            right: obj.rb_right,
        }
    }

    fn pack(&mut self, data: RedBlackData<ObjectData, usize>) -> usize {
        let obj = &mut self.0[data.data.index];
        obj.rb_left = data.left;
        obj.rb_right = data.right;
        data.data.index
    }
}

fn main() {
    let mut objects = Vec::new();
    let mut root = None;
    for i in 1..10 {
        objects.push(Object {
            data: (),
            rb_key: i,
            rb_left: (None, Color::Black),
            rb_right: (None, Color::Black),
        });
        let mut locate = |node: &RedBlackData<ObjectData, usize>, _| match i.cmp(&node.data.key) {
            Ordering::Less => Some((Direction::Left, ())),
            Ordering::Equal => None,
            Ordering::Greater => Some((Direction::Right, ())),
        };
        root = Some(insert(
            root,
            &mut locate,
            ObjectData { index: objects.len() - 1, key: i },
            &mut RbTree(&mut objects),
        ));
    }

    println!("Root: {:?}", root);
    for (i, obj) in objects.iter().enumerate() {
        println!("{}: {:?}", i, obj);
    }

    // Delete the resulting root, to demonstrate that it works.
    root = delete(
        root,
        &mut |_, _: Option<()>| { None },
        &mut RbTree(&mut objects),
    );

    println!("---------");
    println!("Root: {:?}", root);
    for (i, obj) in objects.iter().enumerate() {
        println!("{}: {:?}", i, obj);
    }
}
