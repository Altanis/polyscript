1. Allocation

Heap allocation must occur explicitly, via the `heap` keyword (i.e., `let x = heap 3;`). Escape analysis emits errors
when it detects an escaping reference that points to stack data. Heap allocations take on type `&'heap mut T`, for `T` being the 
type of the expression being heap allocated.

Internally, the data is represented by a struct `Rc<T>` that roughly contains the following attributes:
- `t: T;`: The data the container is holding.
- `ref_count: int;`: The number of existing references to the data.
- `drop: fn();`: The function that runs before the data is freed. In the future, this may be overriden by implementing `Drop` on `T`.
- `clone: fn(Self): Self;`: The function that performs a "shallow copy" of the data. In the future, this may be overriden by implementing `Clone` on `T`.

When a heap allocation occurs, the `Rc` container is allocated and populated with the appropriate data. This marks the
start of the lifetime of the created data.

2. Sharing vs. Cloning

Consider a container `y`, which stores (heap) references to `a_1, a_2, a_3, ... a_n` (for example, `y` could be a struct storing
a heap reference to another struct). Both a "shallow" and "deep" copy of `y` entails  a duplication of the value of `y` in memory. 
However, the shallow copy does not duplicate the values of underlying references in memory, it simply increments their reference
counter. A deep copy entails the underlying references having their values duplicated and stored in the copied container `y`. 
The language does not provide semantics for a deep copy, and this procedure must be implemented manually.

Data that resides in the stack and the heap follow the same semantics when being moved around.
    1. Using data by value, i.e. data with no explicit reference (of type `T`), results in a shallow copy of the data. The data is copied 
    into memory, and escape analysis determines if the copied data will reside in stack or heap memory. The only exception is if the
    value is on the left hand side of an Assignment operation, in which case a mutation occurs on the data.

    2. Using data by reference, i.e. data with an explicit reference (`&T`, `&mut T`, `&'heap T`, `&'heap mut T`), results in a pointer to the data 
    being passed around. If the data resides on the stack, the stack pointer is free to move around, and no reference counting occurs (escape analysis 
    verifies that dangling references to `x` do not escape). If the data resides on the heap, the reference counter is incremented.

    3. Dereferencing a reference to data results in a shallow copy. The only exception is if the dereference is on the left hand of an Assignment 
    operation, in which case a mutation occurs on the data.

    4. Returning data from a function without an explicit reference is not a traditional "use by value." Move semantics are invoked, and no shallow
    copy occurs. If the data is heap allocated, the reference counter is not decremented, as the data is moved.

Consult the following code for reference:
```rs
{
    let a: int = 4;
    let b: int = a; // Shallow copy of `a` occurs.
    let c: &int = &a; // A pointer to `a` is taken. No copy occurs.
    let d: int = *c; // Shallow copy of `a` occurs.
}

// All variables dropped by here.

{
    let a: &'heap mut int = heap 4;
    let b: &'heap mut int = a; // A heap pointer is moved, the refcount increases and no copy occurs.
    let c: int = *b; // Shallow copy of `a` occurs on the stack.
}

// `a` and `b` are dropped, the refcount of the heap allocated `4` goes to 0 and is thus dropped.
```

3. Reference Counting

When a reference is acquired to heap allocated data, the reference counter is incremented. Data follows lexical lifetimes, and
so when a scope is exited, all references inside of it have their reference counter decremented. For reference counters equal
to `0`, the `drop` function pointer is called, and the data is freed from memory, completing the life cycle of the data.

When `drop` is called for a struct, its fields are traversed and heap references have their reference counts decremented.