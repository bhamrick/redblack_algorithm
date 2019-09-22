#![allow(dead_code)]
#![allow(unused_mut)]
#![allow(unused_variables)]

#[derive(Debug)]
pub struct RedBlackData<T, N> {
    pub data: T,
    pub left: (Option<N>, Color),
    pub right: (Option<N>, Color),
}

#[derive(Debug, Eq, Ord, PartialEq, PartialOrd, Hash, Copy, Clone)]
pub enum Direction {
    Left,
    Right,
}

impl Direction {
    pub fn opposite(self) -> Direction {
        match self {
            Direction::Left => Direction::Right,
            Direction::Right => Direction::Left,
        }
    }
}

#[derive(Debug, Eq, Ord, PartialEq, PartialOrd, Hash, Copy, Clone)]
pub enum Color {
    Red,
    Black,
}

pub trait PackContext<T, N> {
    fn pack(&mut self, data: RedBlackData<T, N>) -> N;
    fn unpack(&mut self, node: N) -> RedBlackData<T, N>;
}

/// Insert data into the tree and returns the new root node.
/// 
/// * `locate` is a function that directs us to the location where the insertion
/// should happen. The LA parameter is available as an accumulator to track data
/// during the downward traversal.
/// * `data` is the data to insert.
/// * `context` is a structure that is able to convert nodes to and from their
///   corresponding data.
pub fn insert<L, LA, C, T, N> (root: Option<N>, locate: &mut L, data: T, context: &mut C) -> N where
    L: FnMut(&RedBlackData<T, N>, Option<LA>) -> Option<(Direction, LA)>,
    C: PackContext<T, N>
{
    // Find the insertion location and keep track of the path we took there.
    let mut zipper: Zipper<T, N> = Zipper {
        path: Vec::new(),
        node: root.map(|r| { context.unpack(r) }),
    };
    let mut locate_acc = None;
    loop {
        let locate_result = match zipper.node {
            Some(ref n) => locate(n, locate_acc),
            None => break,
        };
        match locate_result {
            Some((dir, new_acc)) => {
                zipper.down(dir, &mut |x| { context.unpack(x) });
                locate_acc = Some(new_acc);
            }
            None => break,
        }
    }

    // Only insert if we got to an empty location.
    if let None = zipper.node {
        zipper.node = Some(RedBlackData {
            data,
            left: (None, Color::Black),
            right: (None, Color::Black),
        });

        // If this isn't the new root (because the tree is empty), it starts out as red.
        if let Some(s) = zipper.path.last_mut() {
            s.step.1 = Color::Red;
        }

        // During this loop, the zipper node is always red.
        // If there is only one step in the zipper, then the node in question
        // is a child of the root, so no work needs to be done.
        while zipper.path.len() >= 2 {
            let l = zipper.path.len();
            let parent_color = zipper.path[l-2].step.1;
            let uncle_color = zipper.path[l-2].sibling.1;

            match parent_color {
                Color::Black => {
                    // Case 1: Parent is black
                    // No work needs to be done.
                    break;
                }
                Color::Red => {
                    match uncle_color {
                        Color::Red => {
                            // Case 2: Parent is red and uncle is red
                            // Color both of them black, color the grandparent red if it's not
                            // the root, and loop.
                            zipper.path[l-2].step.1 = Color::Black;
                            zipper.path[l-2].sibling.1 = Color::Black;
                            if l >= 3 {
                                zipper.path[l-3].step.1 = Color::Red;
                            }
                            zipper.up(&mut |x| { context.pack(x) });
                            zipper.up(&mut |x| { context.pack(x) });
                        }
                        Color::Black => {
                            // Case 3: Parent is red and uncle is black.
                            // Case 3.1: If the node is "inside" (left child of
                            // right child or vice versa), perform a tree rotation
                            // so that it is on the outside.
                            if zipper.path[l-2].step.0 != zipper.path[l-1].step.0 {
                                zipper.rotate();
                            }
                            // Rotate the parent, recolor previous parent to black,
                            // and previous grandparent to red.
                            zipper.up(&mut |x| { context.pack(x) });
                            zipper.rotate();
                            // After the rotation, the zipper is focused on what
                            // used to be the grandparent.
                            let l = zipper.path.len();
                            if l >= 1 {
                                zipper.path[l-1].step.1 = Color::Red;
                            }
                            if l >= 2 {
                                zipper.path[l-2].step.1 = Color::Black;
                            }
                        }
                    }
                }
            }
        }
    }

    while !zipper.path.is_empty() {
        zipper.up(&mut |x| { context.pack(x) });
    }

    context.pack(zipper.node.unwrap())
}

pub fn delete<L, LA, C, T, N> (root: Option<N>, locate: &mut L, context: &mut C) -> Option<N> where
    L: FnMut(&RedBlackData<T, N>, Option<LA>) -> Option<(Direction, LA)>,
    C: PackContext<T, N>,
{
    // Find node to delete.
    let mut zipper: Zipper<T, N> = Zipper {
        path: Vec::new(),
        node: root.map(|r| { context.unpack(r) }),
    };
    let mut locate_acc = None;
    loop {
        let locate_result = match zipper.node {
            Some(ref n) => locate(n, locate_acc),
            None => break,
        };
        match locate_result {
            Some((dir, new_acc)) => {
                zipper.down(dir, &mut |x| { context.unpack(x) });
                locate_acc = Some(new_acc);
            }
            None => break,
        }
    }

    // Only delete if there's a node here.
    if zipper.node.is_some() {
        // If neither child is empty, swap with the predecessor
        let mut needs_swap = false;
        if let Some(ref n) = zipper.node {
            needs_swap = n.left.0.is_some() && n.right.0.is_some();
        }
        if needs_swap {
            let swap_index = zipper.path.len();
            zipper.down(Direction::Left, &mut |x| { context.unpack(x) });
            while zipper.node.as_ref().unwrap().right.0.is_some() {
                zipper.down(Direction::Right, &mut |x| { context.unpack(x) });
            }
            std::mem::swap(&mut zipper.path[swap_index].data, &mut zipper.node.as_mut().unwrap().data);
        }

        // Replace node with its child. If the child was black,
        // then we have an extra black that we need to add.
        let mut add_black = false;
        if let Some(node) = zipper.node {
            if node.left.0.is_some() {
                zipper.node = node.left.0.map(|x| { context.unpack(x) });
                add_black = node.left.1 == Color::Black;
            } else {
                zipper.node = node.right.0.map(|x| { context.unpack(x) });
                add_black = node.right.1 == Color::Black;
            }
        }

        while add_black {
            match zipper.path.pop() {
                Some(mut s) => {
                    match s.step.1 {
                        Color::Red => {
                            // If the current node is red, we recolor it black and finish.
                            s.step.1 = Color::Black;
                            zipper.path.push(s);
                            add_black = false;
                        }
                        Color::Black => {
                            // This is the "double-black" case.
                            let sibling_color = s.sibling.1;
                            match sibling_color {
                                Color::Black => {
                                    // Start by focusing the zipper on the sibling.
                                    let node = zipper.node.take();
                                    let sibling_direction = s.step.0.opposite();
                                    zipper.path.push(ZipperStep {
                                        data: s.data,
                                        step: (sibling_direction, s.sibling.1),
                                        sibling: (node.map(|x| { context.pack(x) }), s.step.1),
                                    });
                                    // The black height invariant ensures that
                                    // the sibling is never empty. Since we have
                                    // a double black edge, each path down
                                    // the sibling must have at least two black
                                    // edges, but if the sibling were empty, it
                                    // would be only one.
                                    let node = context.unpack(s.sibling.0.unwrap());
                                    let mut red_direction = None;
                                    if node.left.1 == Color::Red {
                                        red_direction = Some(Direction::Left);
                                    } else if node.right.1 == Color::Red {
                                        red_direction = Some(Direction::Right);
                                    }
                                    zipper.node = Some(node);
                                    match red_direction {
                                        Some(red_direction) => {
                                            // If there is a red child, first
                                            // focus the zipper there.
                                            zipper.down(red_direction, &mut |x| { context.unpack(x) });
                                            zipper.path.last_mut().unwrap().step.1 = Color::Black;
                                            if sibling_direction == red_direction {
                                                zipper.up(&mut |x| { context.pack(x) });
                                                zipper.rotate();
                                            } else {
                                                zipper.rotate();
                                                zipper.up(&mut |x| { context.pack(x) });
                                                zipper.rotate();
                                            }
                                            add_black = false;
                                        }
                                        None => {
                                            // If there is no red child, remove a
                                            // black from the double black node and
                                            // its sibling, and add a black to
                                            // its parent.
                                            if let Some(s) = zipper.path.last_mut() {
                                                s.step.1 = Color::Red;
                                            }
                                            zipper.up(&mut |x| { context.pack(x) });
                                        }
                                    }
                                }
                                Color::Red => {
                                    // Red sibling, rebuild this tree and loop.
                                    // On the next iteration, we'll always fall into
                                    // a black sibling case and make progress up the tree.
                                    // Sibling is never empty because it is red.
                                    let unpacked_sibling = context.unpack(s.sibling.0.unwrap());
                                    match s.step.0 {
                                        Direction::Left => {
                                            zipper.path.push(ZipperStep {
                                                data: unpacked_sibling.data,
                                                step: (Direction::Left, Color::Red),
                                                sibling: unpacked_sibling.right,
                                            });
                                            zipper.path.push(ZipperStep {
                                                data: s.data,
                                                step: (Direction::Left, Color::Black),
                                                sibling: unpacked_sibling.left,
                                            });
                                        }
                                        Direction::Right => {
                                            zipper.path.push(ZipperStep {
                                                data: unpacked_sibling.data,
                                                step: (Direction::Right, Color::Red),
                                                sibling: unpacked_sibling.left,
                                            });
                                            zipper.path.push(ZipperStep {
                                                data: s.data,
                                                step: (Direction::Right, Color::Black),
                                                sibling: unpacked_sibling.right,
                                            });
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
                None => {
                    // If the current node is the root, we can just drop the extra black.
                    add_black = false;
                }
            }
        }
    }

    while !zipper.path.is_empty() {
        zipper.up(&mut |x| { context.pack(x) });
    }

    zipper.node.map(|r| { context.pack(r) })
}

// Internal structures
struct ZipperStep<T, N> {
    data: T,
    step: (Direction, Color),
    sibling: (Option<N>, Color),
}

struct Zipper<T, N> {
    path: Vec<ZipperStep<T, N>>,
    node: Option<RedBlackData<T, N>>,
}

impl<T, N> Zipper<T, N> {
    fn up<P>(&mut self, pack: &mut P)
        where P: FnMut(RedBlackData<T, N>) -> N
    {
        if let Some(step) = self.path.pop() {
            let packed_node = self.node.take().map(pack);
            self.node = Some(match step.step.0 {
                Direction::Left => RedBlackData {
                    data: step.data,
                    left: (packed_node, step.step.1),
                    right: step.sibling,
                },
                Direction::Right => RedBlackData {
                    data: step.data,
                    left: step.sibling,
                    right: (packed_node, step.step.1),
                },
            });
        }
    }

    fn down<U>(&mut self, dir: Direction, unpack: &mut U)
        where U: FnMut(N) -> RedBlackData<T, N>
    {
        if let Some(n) = self.node.take() {
            match dir {
                Direction::Left => {
                    self.path.push(ZipperStep {
                        data: n.data,
                        step: (Direction::Left, n.left.1),
                        sibling: n.right,
                    });
                    self.node = n.left.0.map(unpack);
                }
                Direction::Right => {
                    self.path.push(ZipperStep {
                        data: n.data,
                        step: (Direction::Right, n.right.1),
                        sibling: n.left,
                    });
                    self.node = n.right.0.map(unpack);
                }
            }
        }
    }

    // Rotate this node up to the parent, new focus is on the node that was
    // originally the parent, which will be at the same depth as the old focus.
    // The colors of the two nodes gets swapped. For our purposes,
    // this doesn't matter since we only rotate when both nodes are red.
    fn rotate(&mut self) {
        if let Some(n) = self.node.take() {
            if let Some(s) = self.path.pop() {
                match s.step.0 {
                    Direction::Left => {
                        self.path.push(ZipperStep {
                            data: n.data,
                            step: (Direction::Right, s.step.1),
                            sibling: n.left,
                        });
                        self.node = Some(RedBlackData {
                            data: s.data,
                            left: n.right,
                            right: s.sibling,
                        });
                    }
                    Direction::Right => {
                        self.path.push(ZipperStep {
                            data: n.data,
                            step: (Direction::Left, s.step.1),
                            sibling: n.right,
                        });
                        self.node = Some(RedBlackData {
                            data: s.data,
                            left: s.sibling,
                            right: n.left,
                        });
                    }
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use std::cmp::Ordering;

    #[derive(Debug)]
    struct Node {
        data: i32,
        left: (Option<Box<Node>>, Color),
        right: (Option<Box<Node>>, Color),
    }

    fn locate(x: i32) -> impl FnMut(&RedBlackData<i32, Node>, Option<()>) -> Option<(Direction, ())> {
        move |n, _| {
            match x.cmp(&n.data) {
                Ordering::Less => Some((Direction::Left, ())),
                Ordering::Equal => None,
                Ordering::Greater => Some((Direction::Right, ())),
            }
        }
    }

    impl PackContext<i32, Node> for () {
        fn pack(&mut self, data: RedBlackData<i32, Node>) -> Node {
            Node {
                data: data.data,
                left: (data.left.0.map(Box::new), data.left.1),
                right: (data.right.0.map(Box::new), data.right.1),
            }
        }

        fn unpack(&mut self, node: Node) -> RedBlackData<i32, Node> {
            RedBlackData {
                data: node.data,
                left: (node.left.0.map(|x| { *x }), node.left.1),
                right: (node.right.0.map(|x| { *x }), node.right.1),
            }
        }
    }

    fn check_invariants(root: Option<&Node>) {
        // Invariants that are checked:
        // (1) Every path to an empty location has the same number of black nodes.
        // (2) Every empty location is black.
        // (3) Every child of a red node is black.
        fn traverse(
            node: Option<&Node>,
            black_depths: &mut Vec<i32>,
            black_depth: i32,
            color: Color,
        ) {
            match node {
                None => {
                    assert!(color == Color::Black);
                    black_depths.push(black_depth);
                }
                Some(node) => {
                    if color == Color::Red {
                        assert!(node.left.1 == Color::Black);
                        assert!(node.right.1 == Color::Black);
                    }
                    traverse(
                        node.left.0.as_ref().map(Box::as_ref),
                        black_depths,
                        match node.left.1 {
                            Color::Red => black_depth,
                            Color::Black => black_depth+1,
                        },
                        node.left.1,
                    );
                    traverse(
                        node.right.0.as_ref().map(Box::as_ref),
                        black_depths,
                        match node.right.1 {
                            Color::Red => black_depth,
                            Color::Black => black_depth+1,
                        },
                        node.right.1,
                    );
                }
            }
        }

        let mut black_depths = Vec::new();
        traverse(root, &mut black_depths, 0, Color::Black);

        if !black_depths.is_empty() {
            let black_depth = black_depths[0];
            for d in black_depths {
                assert!(d == black_depth);
            }
        }
    }

    fn check_ordering(root: Option<&Node>) {
        // For each node, check that each value in the left subtree is lesser
        // and each value in the right subtree is greater.
        fn traverse(
            node: Option<&Node>,
            lower_bound: Option<i32>,
            upper_bound: Option<i32>,
        ) {
            if let Some(node) = node {
                if let Some(lower_bound) = lower_bound {
                    assert!(node.data > lower_bound);
                }
                if let Some(upper_bound) = upper_bound {
                    assert!(node.data < upper_bound);
                }
                traverse(
                    node.left.0.as_ref().map(Box::as_ref),
                    lower_bound,
                    Some(node.data),
                );
                traverse(
                    node.right.0.as_ref().map(Box::as_ref),
                    Some(node.data),
                    upper_bound,
                );
            }
        }
    }

    #[test]
    fn inserts() {
        let mut root: Option<Node> = None;
        check_invariants(root.as_ref());
        check_ordering(root.as_ref());
        root = Some(insert(root, &mut locate(5), 5, &mut ()));
        check_invariants(root.as_ref());
        check_ordering(root.as_ref());
        root = Some(insert(root, &mut locate(7), 7, &mut ()));
        check_invariants(root.as_ref());
        check_ordering(root.as_ref());
        root = Some(insert(root, &mut locate(4), 4, &mut ()));
        check_invariants(root.as_ref());
        check_ordering(root.as_ref());
        root = Some(insert(root, &mut locate(3), 3, &mut ()));
        check_invariants(root.as_ref());
        check_ordering(root.as_ref());
        for i in 1 .. 100 {
            root = Some(insert(root, &mut locate(i), i, &mut ()));
            check_invariants(root.as_ref());
            check_ordering(root.as_ref());
        }
    }

    #[test]
    fn insert_and_delete() {
        let insert_order = [3, 2, 1, 4, 5, 6];
        let delete_order = [4, 6, 2, 5, 1, 3];
        let mut root = None;
        for x in insert_order.iter().cloned() {
            root = Some(insert(root, &mut locate(x), x, &mut ()));
            check_invariants(root.as_ref());
            check_ordering(root.as_ref());
        }
        println!("{:?}", root);
        for x in delete_order.iter().cloned() {
            println!("Delete {}", x);
            root = delete(root, &mut locate(x), &mut ());
            println!("{:?}", root);
            check_invariants(root.as_ref());
            check_ordering(root.as_ref());
        }
    }
}
