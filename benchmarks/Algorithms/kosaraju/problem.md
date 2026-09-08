# Kosaraju Strongly Connected Components

## Problem Description

Given a directed graph in compressed sparse row (CSR) form, compute its strongly connected components with Kosaraju's algorithm. Assign a label to every vertex so that two vertices receive the same label exactly when each is reachable from the other.

## Input

The function receives the number of vertices `n`, the CSR column and row arrays `fadj_col` and `fadj_row`, and an output array `sid` of length `n`.

## Output

The function writes the component labels to `sid`. For every pair of valid vertices `u` and `v`, `sid[u] == sid[v]` holds exactly when `u` and `v` are mutually reachable. The input CSR arrays are preserved.

## Constraints

- `1 <= n <= 2147483646`.
- The CSR arrays form a valid representation of a directed graph with `n` vertices.
- Every stored endpoint is a valid vertex.
- The graph contains at least one edge.
- All array lengths and arithmetic satisfy the bounds in the function contract.

## Source

Classical Kosaraju strongly connected components algorithm; formalized from the QCP verified C artifact.
