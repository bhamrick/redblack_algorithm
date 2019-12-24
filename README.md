`redblack_algorithm` is a generic implementation of a [red-black
tree](https://en.wikipedia.org/wiki/Red%E2%80%93black_tree).  The red-black
algorithm is very useful as a general way to keep a tree balanced in many
contexts other than a simple binary search tree, and also without imposing a
particular data representation.

The functions have several type parameters:

* `T` is the type of data being stored in each node of the tree. Since the
  method of locating positions in the tree is left unspecified, there is no
  distinction between keys and values. If you need both, `T` should contain
  both.
* `N` is the representation of a "packed" node. A packed node is the at-rest
  data representation. An unpacked node is the data stored and information about
  its children, which is used in the process of the tree manipulation functions.
* `C` is a `PackContext` which enables the conversion between `N` and
  `RedBlackData<T, N>`.
* `L` is a function that directs the insertion and deletion functions to the
  node in question. For example, in the case of a regular binary search tree,
  the locator would be a closure that compares the value being inserted against
  the values in the tree.
* `LA` is an accumulator for the locator function, which allows for a stateful
  traversal down the tree. In simple cases, `LA` can be `()`.

Generally, it is expected that users of this library define a wrapper type and
wrapper functions to create a simpler interface. See the examples.

The current implementation uses zippers that are represented with Vecs, so
despite the at-rest data representation being flexible, it does depend on having
access to allocation.
