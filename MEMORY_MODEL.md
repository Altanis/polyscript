1. Allocation

Heap allocation must occur explicitly, via the `heap` keyword (i.e., `let x = heap 3;`). Escape analysis emits errors
when it detects an escaping reference that points to stack data. Heap allocations take on type `T`, for `T` being the 
type of the expression being heap allocated.

Internally, the data is represented by a struct `Rc<T>` that contains the following attributes:
- `t: T;`: The data the container is holding.
- `ref_count: int;`: The number of existing references to the data.
- `drop: fn();`: The function that frees the data. In the future, this may be overriden by implementing `Drop` on `T`.

When a heap allocation occurs, the `Rc` container is allocated and populated with the appropriate data. This marks the
start of the lifetime of the created data.

2. Sharing vs. Cloning

Data that resides in the stack and the heap follow the same semantics when being moved around. Consider the value `x`,
a variable that holds data that can reside in either place. The following rules on `x` apply:

    1. Using `x` by value, such as `let y = x;` or `func(x)`, results in a shallow copy of `x`. The data is copied into memory,
    and escape analysis determines if the copied data will reside in stack or heap memory. The only exception is if the value
    is on the left hand side of an Assignment operation, in which case a simple mutation occurs on `x`.

    2. Using `x` by reference, such as `let y = &x` or `func(&x)`, results in a pointer to `x` being passed around. If `x`
    resides on the stack, the stack pointer is free to move around, and no reference counting occurs (escape analysis verifies
    that dangling references to `x` do not escape). If `x` resides on the heap, the reference counter is incremented.

    3. Dereferencing a reference to `x`, such as `let y = *&x;` or `func(*&x)`, results in a shallow copy. The only exception is
    if the dereference is on the left hand of an Assignment operation, in which case a simple mutation occurs on `x`.

    4. Returning `x` from a function is not a traditional "use by value." Move semantics are invoked, and no shallow copy occurs.
    If `x` is heap allocated, the reference counter is not decremented, as `x` is moved.

Consider a container `y`, which stores (heap) references to `a_1, a_2, a_3, ... a_n`. A "shallow copy" of `y` entails an increment in
the reference counters for each reference, while a "deep copy" entails the underlying reference is cloned and replaced with a unique
value. The language does not provide semantics for a deep copy, and this procedure must be implemented manually.

3. Reference Counting

When a reference is acquired to heap allocated data, the reference counter is incremented. Data follows lexical lifetimes, and
so when a scope is exited, all references inside of it have their reference counter decremented. For reference counters equal
to `0`, the `drop` function pointer is called, and the data is freed from memory, completing the life cycle of the data.

The `drop` function will be `NULL` for immediates that do not require true deallocation. Structs will have a default
`drop` implementation that recurses through its fields and then frees the struct memory itself.