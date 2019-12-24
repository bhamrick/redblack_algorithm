//! `redblack_algorithm` is a generic implementation of a
//! [red-black tree](https://en.wikipedia.org/wiki/Red%E2%80%93black_tree).
//! The red-black algorithm is very useful as a general way to keep a tree
//! balanced in many contexts other than a simple binary search tree, and also
//! without imposing a particular data representation.
//!
//! The functions have several type parameters:
//!
//! * `T` is the type of data being stored in each node of the tree. Since the
//! method of locating positions in the tree is left unspecified, there is no
//! distinction between keys and values. If you need both, `T` should contain
//! both.
//! * `N` is the representation of a "packed" node. A packed node is the at-rest
//! data representation. An unpacked node is the data stored and information
//! about its children, which is used in the process of the tree manipulation
//! functions.
//! * `C` is a `PackContext` which enables the conversion between `N` and
//! `RedBlackData<T, N>`.
//! * `L` is a function that directs the insertion and deletion functions to the
//! node in question. For example, in the case of a regular binary search tree,
//! the locator would be a closure that compares the value being inserted
//! against the values in the tree.
//! * `LA` is an accumulator for the locator function, which allows for a
//! stateful traversal down the tree. In simple cases, `LA` can be `()`.
//!
//! Generally, it is expected that users of this library define a wrapper type
//! and wrapper functions to create a simpler interface. See the examples.
//!
//! The current implementation uses zippers that are represented with Vecs, so
//! despite the at-rest data representation being flexible, it does depend on
//! having access to allocation.

/// An "unpacked" representation of a node.
///
/// Following the library-wide naming conventions:
///
/// * `T` is the type of data being stored.
/// * `N` is the representation of a packed node.
///
/// Here we take a slightly different approach to coloring nodes than standard
/// presentations.  Instead of the color being stored on a node, it is stored on
/// the link from a parent to a child, which saves us some packs and unpacks.
#[derive(Debug)]
pub struct RedBlackData<T, N> {
    pub data: T,
    pub left: Option<(N, Color)>,
    pub right: Option<(N, Color)>,
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
/// * `locate` is a function that directs us to the location where the insertion should happen. The
/// `LA` parameter is available as an accumulator to track data during the downward traversal.
/// * `data` is the data to store in the inserted node.
/// * `context` is a structure that can convert between `N` and `RedBlackData<T, N>`.
///
/// If `locate` returns `None` at an existing node, no insertion occurs.
pub fn insert<L, LA, C, T, N>(root: Option<N>, locate: &mut L, data: T, context: &mut C) -> N
where
    L: FnMut(&RedBlackData<T, N>, Option<LA>) -> Option<(Direction, LA)>,
    C: PackContext<T, N>,
{
    // Find the insertion location and keep track of the path we took there.
    let mut zipper: Zipper<T, N> = Zipper {
        path: Vec::new(),
        node: root.map(|r| context.unpack(r)),
    };
    let mut locate_acc = None;
    loop {
        let locate_result = match zipper.node {
            Some(ref n) => locate(n, locate_acc),
            None => break,
        };
        match locate_result {
            Some((dir, new_acc)) => {
                zipper.down(dir, &mut |x| context.unpack(x));
                locate_acc = Some(new_acc);
            }
            None => break,
        }
    }

    // Only insert if we got to an empty location.
    if let None = zipper.node {
        zipper.node = Some(RedBlackData {
            data,
            left: None,
            right: None,
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
            let parent_color = zipper.path[l - 2].step.1;
            let uncle_color = color(&zipper.path[l - 2].sibling);

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
                            zipper.path[l - 2].step.1 = Color::Black;
                            // Unwrap: Since the uncle color is red, the uncle
                            // node must exist.
                            zipper.path[l - 2].sibling.as_mut().unwrap().1 = Color::Black;
                            if l >= 3 {
                                zipper.path[l - 3].step.1 = Color::Red;
                            }
                            zipper.up(&mut |x| context.pack(x));
                            zipper.up(&mut |x| context.pack(x));
                        }
                        Color::Black => {
                            // Case 3: Parent is red and uncle is black.
                            // Case 3.1: If the node is "inside" (left child of
                            // right child or vice versa), perform a tree rotation
                            // so that it is on the outside.
                            if zipper.path[l - 2].step.0 != zipper.path[l - 1].step.0 {
                                zipper.rotate();
                            }
                            // Rotate the parent, recolor previous parent to black,
                            // and previous grandparent to red.
                            zipper.up(&mut |x| context.pack(x));
                            zipper.rotate();
                            // After the rotation, the zipper is focused on what
                            // used to be the grandparent.
                            let l = zipper.path.len();
                            if l >= 1 {
                                zipper.path[l - 1].step.1 = Color::Red;
                            }
                            if l >= 2 {
                                zipper.path[l - 2].step.1 = Color::Black;
                            }
                        }
                    }
                }
            }
        }
    }

    while !zipper.path.is_empty() {
        zipper.up(&mut |x| context.pack(x));
    }

    // Unwrap: After the above loop, zipper always points to the root of the
    // tree if it exists, and the tree cannot be empty because we would have
    // inserted a node into an empty tree.
    context.pack(zipper.node.unwrap())
}

/// Remove a node from the tree, returning the new root node if it exists.
///
/// * `locate` is a function that directs us to the node that should be deleted. The `LA`
/// parameter is available as an accumulator to track data during the downward traversal.
/// * `context` is a structure that can convert between `N` and `RedBlackData<T, N>`.
pub fn delete<L, LA, C, T, N>(root: Option<N>, locate: &mut L, context: &mut C) -> Option<N>
where
    L: FnMut(&RedBlackData<T, N>, Option<LA>) -> Option<(Direction, LA)>,
    C: PackContext<T, N>,
{
    // Find node to delete.
    let mut zipper: Zipper<T, N> = Zipper {
        path: Vec::new(),
        node: root.map(|r| context.unpack(r)),
    };
    let mut locate_acc = None;
    loop {
        let locate_result = match zipper.node {
            Some(ref n) => locate(n, locate_acc),
            None => break,
        };
        match locate_result {
            Some((dir, new_acc)) => {
                zipper.down(dir, &mut |x| context.unpack(x));
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
            needs_swap = n.left.is_some() && n.right.is_some();
        }
        if needs_swap {
            let swap_index = zipper.path.len();
            zipper.down(Direction::Left, &mut |x| context.unpack(x));
            // Unwrap: zipper.node.is_some() checked above.
            while zipper.node.as_ref().unwrap().right.is_some() {
                zipper.down(Direction::Right, &mut |x| context.unpack(x));
            }
            std::mem::swap(
                &mut zipper.path[swap_index].data,
                // Unwrap: zipper.node.is_some() checked above.
                &mut zipper.node.as_mut().unwrap().data,
            );
        }

        // Replace node with its child. If the child was black,
        // then we have an extra black that we need to add.
        let mut add_black = false;
        if let Some(node) = zipper.node {
            if let Some((n, c)) = node.left {
                add_black = c == Color::Black;
                zipper.node = Some(context.unpack(n));
            } else {
                add_black = color(&node.right) == Color::Black;
                zipper.node = node.right.map(|(n, _)| context.unpack(n));
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
                            let sibling_color = color(&s.sibling);
                            match sibling_color {
                                Color::Black => {
                                    // Start by focusing the zipper on the sibling.
                                    let node = zipper.node.take();
                                    let sibling_direction = s.step.0.opposite();
                                    zipper.path.push(ZipperStep {
                                        data: s.data,
                                        step: (sibling_direction, color(&s.sibling)),
                                        sibling: node.map(|x| (context.pack(x), Color::Black)),
                                    });
                                    // Unwrap: The black height invariant
                                    // ensures that the sibling is never empty.
                                    // Since we have a double black edge, each
                                    // path down the sibling must have at least
                                    // two black edges, but if the sibling were
                                    // empty, it would be only one.
                                    let node = context.unpack(s.sibling.unwrap().0);
                                    let mut red_direction = None;
                                    if color(&node.left) == Color::Red {
                                        red_direction = Some(Direction::Left);
                                    } else if color(&node.right) == Color::Red {
                                        red_direction = Some(Direction::Right);
                                    }
                                    zipper.node = Some(node);
                                    match red_direction {
                                        Some(red_direction) => {
                                            // If there is a red child, first
                                            // focus the zipper there.
                                            zipper.down(red_direction, &mut |x| context.unpack(x));
                                            // Unwrap: zipper.path is always
                                            // nonempty after a call to down()
                                            zipper.path.last_mut().unwrap().step.1 = Color::Black;
                                            if sibling_direction == red_direction {
                                                zipper.up(&mut |x| context.pack(x));
                                                zipper.rotate();
                                            } else {
                                                zipper.rotate();
                                                zipper.up(&mut |x| context.pack(x));
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
                                            zipper.up(&mut |x| context.pack(x));
                                        }
                                    }
                                }
                                Color::Red => {
                                    // Red sibling, rebuild this tree and loop.
                                    // On the next iteration, we'll always fall
                                    // into a black sibling case and make
                                    // progress up the tree.
                                    // Unwrap: Sibling is never empty because it is red.
                                    let unpacked_sibling = context.unpack(s.sibling.unwrap().0);
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
        zipper.up(&mut |x| context.pack(x));
    }

    zipper.node.map(|r| context.pack(r))
}

// Internal structures
struct ZipperStep<T, N> {
    data: T,
    step: (Direction, Color),
    sibling: Option<(N, Color)>,
}

struct Zipper<T, N> {
    path: Vec<ZipperStep<T, N>>,
    node: Option<RedBlackData<T, N>>,
}

impl<T, N> Zipper<T, N> {
    fn up<P>(&mut self, pack: &mut P)
    where
        P: FnMut(RedBlackData<T, N>) -> N,
    {
        if let Some(step) = self.path.pop() {
            let link = self.node.take().map(|x| (pack(x), step.step.1));
            self.node = Some(match step.step.0 {
                Direction::Left => RedBlackData {
                    data: step.data,
                    left: link,
                    right: step.sibling,
                },
                Direction::Right => RedBlackData {
                    data: step.data,
                    left: step.sibling,
                    right: link,
                },
            });
        }
    }

    fn down<U>(&mut self, dir: Direction, unpack: &mut U)
    where
        U: FnMut(N) -> RedBlackData<T, N>,
    {
        if let Some(n) = self.node.take() {
            match dir {
                Direction::Left => {
                    self.path.push(ZipperStep {
                        data: n.data,
                        step: (Direction::Left, color(&n.left)),
                        sibling: n.right,
                    });
                    self.node = n.left.map(|(n, _)| unpack(n));
                }
                Direction::Right => {
                    self.path.push(ZipperStep {
                        data: n.data,
                        step: (Direction::Right, color(&n.right)),
                        sibling: n.left,
                    });
                    self.node = n.right.map(|(n, _)| unpack(n));
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

#[inline(always)]
fn color<N>(link: &Option<(N, Color)>) -> Color {
    match link {
        Some((_, c)) => *c,
        None => Color::Black,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use std::cmp::Ordering;
    use std::collections::HashSet;

    use proptest::prelude::*;

    #[derive(Debug)]
    struct Node {
        data: i32,
        left: Option<(Box<Node>, Color)>,
        right: Option<(Box<Node>, Color)>,
    }

    fn locate(
        x: i32,
    ) -> impl FnMut(&RedBlackData<i32, Node>, Option<()>) -> Option<(Direction, ())> {
        move |n, _| match x.cmp(&n.data) {
            Ordering::Less => Some((Direction::Left, ())),
            Ordering::Equal => None,
            Ordering::Greater => Some((Direction::Right, ())),
        }
    }

    impl PackContext<i32, Node> for () {
        fn pack(&mut self, data: RedBlackData<i32, Node>) -> Node {
            Node {
                data: data.data,
                left: data.left.map(|(n, c)| (Box::new(n), c)),
                right: data.right.map(|(n, c)| (Box::new(n), c)),
            }
        }

        fn unpack(&mut self, node: Node) -> RedBlackData<i32, Node> {
            RedBlackData {
                data: node.data,
                left: node.left.map(|(x, c)| (*x, c)),
                right: node.right.map(|(x, c)| (*x, c)),
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
            link_color: Color,
        ) {
            match node {
                None => {
                    assert!(link_color == Color::Black);
                    black_depths.push(black_depth);
                }
                Some(node) => {
                    if link_color == Color::Red {
                        assert!(color(&node.left) == Color::Black);
                        assert!(color(&node.right) == Color::Black);
                    }
                    traverse(
                        node.left.as_ref().map(|(n, _)| n.as_ref()),
                        black_depths,
                        match color(&node.left) {
                            Color::Red => black_depth,
                            Color::Black => black_depth + 1,
                        },
                        color(&node.left),
                    );
                    traverse(
                        node.right.as_ref().map(|(n, _)| n.as_ref()),
                        black_depths,
                        match color(&node.right) {
                            Color::Red => black_depth,
                            Color::Black => black_depth + 1,
                        },
                        color(&node.right),
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
        fn traverse(node: Option<&Node>, lower_bound: Option<i32>, upper_bound: Option<i32>) {
            if let Some(node) = node {
                if let Some(lower_bound) = lower_bound {
                    assert!(node.data >= lower_bound);
                }
                if let Some(upper_bound) = upper_bound {
                    assert!(node.data <= upper_bound);
                }
                traverse(
                    node.left.as_ref().map(|(n, _)| n.as_ref()),
                    lower_bound,
                    Some(node.data),
                );
                traverse(
                    node.right.as_ref().map(|(n, _)| n.as_ref()),
                    Some(node.data),
                    upper_bound,
                );
            }
        }

        traverse(root, None, None)
    }

    fn value_set(root: Option<&Node>) -> HashSet<i32> {
        fn traverse(node: Option<&Node>, values: &mut HashSet<i32>) {
            if let Some(node) = node {
                values.insert(node.data);
                traverse(node.left.as_ref().map(|(n, _)| n.as_ref()), values);
                traverse(node.right.as_ref().map(|(n, _)| n.as_ref()), values);
            }
        }

        let mut values = HashSet::new();
        traverse(root, &mut values);
        values
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
        for i in 1..100 {
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
        let mut expected_values = HashSet::new();
        for x in insert_order.iter().cloned() {
            root = Some(insert(root, &mut locate(x), x, &mut ()));
            expected_values.insert(x);
            check_invariants(root.as_ref());
            check_ordering(root.as_ref());
            assert!(value_set(root.as_ref()) == expected_values);
        }
        for x in delete_order.iter().cloned() {
            root = delete(root, &mut locate(x), &mut ());
            check_invariants(root.as_ref());
            check_ordering(root.as_ref());
        }
    }

    static VALUES: &'static [i32] = &[
        0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 18, 18,
    ];
    proptest! {
        #[test]
        fn insert_and_delete_props(
            insert_order in Just(VALUES.to_owned()).prop_shuffle(),
            delete_order in Just(VALUES.to_owned()).prop_shuffle(),
        ) {
            let mut root = None;
            let mut expected_values = HashSet::new();
            for x in insert_order.iter().cloned() {
                root = Some(insert(root, &mut locate(x), x, &mut ()));
                expected_values.insert(x);
                check_invariants(root.as_ref());
                check_ordering(root.as_ref());
                assert!(value_set(root.as_ref()) == expected_values);
            }
            for x in delete_order.iter().cloned() {
                root = delete(root, &mut locate(x), &mut ());
                check_invariants(root.as_ref());
                check_ordering(root.as_ref());
            }
        }
    }
}
