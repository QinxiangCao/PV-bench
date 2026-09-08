# 0/1 Knapsack

## Description

Choose a subset of items, each at most once, to maximize total value without exceeding the capacity.

## Input

The verification-case input consists of parallel `weights` and `values` arrays, item count `n`, capacity, and a writable DP table.

## Output

The function produces the maximum achievable total value.

## Constraints

- Item weights are positive; values and the capacity are nonnegative; the DP table has $(n+1)(capacity+1)$ cells.

## Source

Classical algorithmic problem reconstructed from the verified C artifact.
