//! An intrusive red-black tree, meaning the tree information is stored within objects that are
//! managed externally.

use std::cmp::Ordering;

use redblack_algorithm::*;

#[derive(Debug)]
struct Object {
    data: (),
    rb_data: Option<RedBlackData<i32, usize>>,
}

struct RbTree<'a>(&'a mut [Object]);

struct ObjectData {
    index: usize,
    key: i32,
}

// The PackContext here gives us access to a slice of objects that we can index into, but unlike in
// the persistent example, we don't allocate new objects and instead modify the existing ones.
impl<'a> PackContext<ObjectData, usize> for RbTree<'a> {
    fn unpack(&mut self, index: usize) -> RedBlackData<ObjectData, usize> {
        let obj = &mut self.0[index];
        let rb_data = obj.rb_data.take().expect("Cannot unpack node that's not in the tree");
        RedBlackData {
            data: ObjectData {
                index,
                key: rb_data.data,
            },
            left: rb_data.left,
            right: rb_data.right,
        }
    }

    fn pack(&mut self, data: RedBlackData<ObjectData, usize>) -> usize {
        let obj = &mut self.0[data.data.index];
        obj.rb_data = Some(RedBlackData {
            data: data.data.key,
            left: data.left,
            right: data.right,
        });
        data.data.index
    }
}

fn main() {
    let mut objects = Vec::new();
    let mut root = None;
    for i in 1..10 {
        objects.push(Object {
            data: (),
            rb_data: None,
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
