must explicitly specify type for T when using a static method on Type<T>, i.e. `[Type<T>].Member` or `[Type<int>].Member`

Notes on references:
1. Aliasing is allowed (mutable references are NOT exclusive).
2. Passing by value => clone of the data, passing by reference => either refcounted or stack ptr.
3. Dereferencing `&T` makes a deep clone of the data (`T`). Dereferencing `&^n T` gives `&^{n - 1} T`, with its refcount increased by 1.
4. `heap` expressions return `&mut T`.

NOTE: Trailing commas are NOT allowed.