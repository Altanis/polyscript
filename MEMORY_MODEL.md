## 1. Allocation

Heap allocation must occur explicitly, via the `heap` keyword (i.e., `let x = heap 3;`). Escape analysis emits errors when it detects an escaping reference that points to stack data. Heap allocations take on type `&'heap mut T`, for `T` being the type of the expression being heap allocated.

Internally, the data is represented by a struct `Rc<T>` that roughly contains the following attributes:

* `t: T;`: The data the container is holding.
* `ref_count: int;`: The number of existing references to the data.
* `deallocate: fn(Self);`: The function that runs when the `Rc` has a reference count of zero.
* `clone: fn(Self): Self;`: The function that performs a "shallow copy" of the data.

When a heap allocation occurs, the `Rc` container is allocated and populated with the appropriate data. This marks the start of the lifetime of the created data.

---

## 2. Sharing vs. Cloning

Consider a container `y`, which stores (heap) references to `a_1, a_2, a_3, ... a_n` (for example, `y` could be a struct storing a heap reference to another struct). Both a "shallow" and "deep" copy of `y` entails a duplication of the value of `y` in memory.

* **Shallow copy** does not duplicate the values of underlying references in memory; it simply increments their reference counter.
* **Deep copy** entails the underlying references having their values duplicated and stored in the copied container `y`.

The language does not provide semantics for a deep copy. This procedure must be implemented manually.

---

## 2.1. BitCopy and Clone

To unify stack and heap duplication semantics, two traits exist:

* **BitCopy**: A marker trait meaning the type may be duplicated by raw bitwise copy.

  * Examples: integers, booleans, plain stack structs, stack references (`&T`, `&mut T`).
  * No destructor is allowed on `BitCopy` types.
  * Standard library containers may `memcpy` elements when `U: BitCopy`.

* **Clone**: A trait for semantic duplication when raw memcpy is not sufficient.

  * Examples: heap references (`&'heap T`, `&'heap mut T`), resource-owning types.
  * `Clone` may run arbitrary code, including reference count increments.
  * Containers like `Vec<T>` call `Clone::clone` element-wise when `U: Clone`.

**Rules:**

* `BitCopy` types are duplicated with no runtime cost.
* Non-`BitCopy` types that need duplication semantics must implement `Clone`.
* Types that must not be duplicated (e.g., unique heap handles) should implement neither `BitCopy` nor `Clone`.

---

## 2.2. Moving and Copying

Data that resides in the stack and the heap follow the same semantics when being moved around:

1. **Use by value** (`T`): Results in a shallow copy. The data is copied into memory, and escape analysis determines if the copied data resides on stack or heap.

   * If `T: BitCopy`, this is a raw memcpy.
   * If `T: Clone`, libraries that need duplication must explicitly call `clone()`.

2. **Use by reference** (`&T`, `&mut T`, `&'heap T`, `&'heap mut T`): Results in a pointer being passed.

   * Stack references: no reference counting.
   * Heap references: reference counter is incremented automatically.

3. **Dereference** (`*r`): Produces a shallow copy of the value.

   * If the dereference is on the left-hand side of an assignment, mutation occurs.

4. **Return by move**: Returning data without an explicit reference invokes move semantics.

   * No shallow copy occurs.
   * Heap references are moved without decrementing the refcount.

---

### Example

```rs
{
    let a: int = 4;
    let b: int = a;      // Shallow copy of `a` occurs (BitCopy).
    let c: &int = &a;    // Pointer to `a` taken. No copy.
    let d: int = *c;     // Shallow copy of `a` occurs.
}

{
    let a: &'heap mut int = heap 4;
    let b: &'heap mut int = a; // Heap pointer moved, refcount incremented.
    let c: int = *b;           // Shallow copy of `a` occurs (stack).
}
```

---

## 3. Dropping

* **Stack data**: Dropped trivially; no action occurs by default.
* **Heap data**: Reference count is decremented.

Both behaviors always occur. Extra behavior may be programmed before refcount changes by implementing the `Drop` trait:

```rs
trait Drop {
    fn drop(&mut self);
}
```

Once `drop` completes, the reference count is decremented. When the reference count reaches zero, `deallocate` is invoked.

---

## 4. Reference Counting

When a reference to heap data is acquired, the reference counter is incremented. Data follows lexical lifetimes. When a scope exits:

* All variables are dropped.
* All heap references have their refcounts decremented.
* If a refcount reaches zero, the `deallocate` function is called.

When `deallocate` is called for a struct:

* Its fields are traversed.
* Heap references inside are decremented recursively.

---

## 5. Containers and Clone

Containers such as `Vec<T>` use these rules to determine cloning:

* If `T: BitCopy`: the buffer is duplicated with a raw `memcpy`.
* If `T: Clone`: elements are duplicated with `T::clone`, which for heap handles increments the reference counter.
* If `T` implements neither: `Vec<T>: Clone` is disallowed.

This ensures containers handle both stack and heap data correctly, with compile-time enforcement.