# Array-Based Priority Queue

## Problem Description

Build, update, pop, and sort an integer heap represented by an array.

## Required Function Contracts

This task specifies a multi-function API. Provide a separate `Require` / `Ensure` contract on **each** of the following functions in `solution.c`:

- `push`
- `build`
- `pop`
- `heap_sort`

Every function listed above is a specification target, including functions called internally by other operations. A contract only on the final or highest-level operation is incomplete. Keep the existing C signatures and bodies unchanged; no loop annotations are requested.

## Input

The functions receive the array representation, its logical size or capacity, and the operation-specific values described by their C signatures.

## Output

Each operation returns or updates the represented data structure according to its interface contract.

## Constraints

All indices, sizes, capacities, and stored values satisfy the bounds stated by the corresponding function contract.

## Source

Classical data-structure implementation reconstructed from the verified C artifact.

