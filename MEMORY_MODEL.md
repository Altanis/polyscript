## Memory Management Traits

The traits `Clone` and `Drop` are provided to the user, which are self explanatory. 
* Cloning a value will invoke the `Clone` implementation for its type.
    * All data has a default `Clone` implementation, which is a simple bitwise copy.
* The `Drop` implementation may not be explicitly invoked for a value.

---

## Heap Allocation

Heap allocations must occur explicitly using the `heap` keyword (i.e., `let x = heap 3` allocates an integer `3` on the stack). Heap allocations take on the type `Heap<T>`, where `T` is the type being allocated. Heap allocations are backed by reference counting structures implicitly, and the lifetime of heap allocations are managed that way.

`Heap<T>` implements the following traits:
* `Clone`: When `Heap<T>` is cloned, the underlying data is not duplicated, rather the reference count increases.
* `Drop`: When `Heap<T>` is dropped, the underlying data is not destroyed, rather the reference count decreases.
* `Deref`: When `Heap<T>` is dereferenced in a r-value position, the underlying data is cloned and given.
* `DerefMut`: When `Heap<T>` is dereferenced in an l-value position, the underlying data is mutated.

`Heap<T>` has no helper methods.

---

## Movement of Data

Implicit clones occur when:
* Data is moved by value.
* A reference to data is dereferenced.