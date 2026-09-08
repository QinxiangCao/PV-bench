# Depth-First Search on an Adjacency List

## Problem Description

Given a directed graph whose vertices are numbered from `0` to `vertex_count - 1`, perform a depth-first search starting from a valid source vertex. The graph is stored as an array of linked lists: `adjacency[u]` contains exactly the outgoing neighbors of vertex `u`.

The graph representation is read-only. The procedure updates the caller-provided `visited` array so that, when it returns, a vertex is marked if and only if it is reachable from the source vertex.

## Input

- `adjacency`: an array of linked-list heads representing all outgoing adjacency lists.
- `vertex_count`: the number of vertices.
- `visited`: an integer array of length `vertex_count`, initially marking no vertex as visited.
- `vertex`: the source vertex from which the traversal starts.

## Output

The function returns no value. It updates `visited` in place so that exactly the vertices reachable from `vertex` are marked as visited. The graph stored in `adjacency` is unchanged.

## Constraints

- `0 < vertex_count < INT_MAX`.
- `0 <= vertex < vertex_count`.
- Every neighbor appearing in an adjacency list is a valid vertex.
- The graph representation is well formed.
- The initial visited set is empty.

## Source

Classical depth-first search problem reconstructed from the verified C artifact.

