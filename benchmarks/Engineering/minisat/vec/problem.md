# MiniSat Vector

## Problem Description

Implement dynamically growing integer and pointer vectors in the style used by MiniSat.
The behavior below applies to both the `veci_*` integer-vector functions and the
`vecp_*` pointer-vector functions.

## Input

Each function receives a vector object and any size, element, or pointer arguments described by its C signature.
`new` receives writable storage for a vector object that does not currently own
a backing buffer. The other operations require a live vector: an initialized,
not-yet-deleted vector with a non-null backing buffer, capacity at least 4, and
`0 <= size <= capacity`. Its logical contents are the first `size` elements of
the buffer.

## Output

- `new` creates an empty vector with size 0 and capacity 4, allocating a
  non-null backing buffer.
- `begin` returns the backing-buffer pointer; `size` returns the logical size.
  Neither operation changes the vector.
- `push` appends the given element, preserving the previous elements in order
  and increasing the size by one. If space remains (`old_size < old_capacity`),
  the buffer pointer and capacity are unchanged. If the vector is full, the
  capacity becomes `2 * old_capacity + 1`; the buffer pointer may change or
  remain the same.
- `resize(k)` only shrinks the logical contents (or leaves them unchanged): it
  requires `0 <= k <= old_size` and retains exactly the first `k` elements.
  The buffer pointer and capacity are unchanged; it does not grow the vector
  or release its allocation.
- `delete` frees the backing buffer, leaving the vector object available for
  reinitialization with `new`. The vector is no longer live, and its fields
  need not be reset. For pointer vectors, stored pointers are values only;
  deleting or shrinking the vector does not free the objects they point to.

## Constraints

Allocation and reallocation are assumed to succeed; allocation-failure handling
is outside this problem. This assumption does not remove the arithmetic bounds:

- Sizes and capacities fit in a signed 32-bit integer, with
  `4 <= capacity <= 2147483647`.
- Let `element_size` be `sizeof(int)` for integer vectors and `sizeof(void *)`
  for pointer vectors. Allocation byte counts satisfy
  `capacity * element_size <= 4294967295`, and the backing allocation must fit
  in the target address space.
- A `push` on a full vector additionally requires `old_capacity <= 1073741823`,
  `(2 * old_capacity + 1) * element_size <= 4294967295`, and a grown allocation
  that fits in the target address space. These ensure that capacity growth and
  allocation-size arithmetic do not overflow.

## Source

MiniSat vector implementation adapted by the QCP LLM benchmark suite.
