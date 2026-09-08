# Overflow-Safe Modular Multiplication

## Description

Compute the signed modular product of two integers by repeated doubling without directly multiplying them.

## Input

The function receives integers $a$, $b$, and a positive modulus.

## Output

Return a representative congruent to $ab$ modulo the modulus.

## Constraints

- $-modulus < a < modulus$.
- `b` fits signed C `int`.
- $0 < modulus$ and $2\,modulus \le \texttt{INT_MAX}$.

## Source

Classical modular-arithmetic problem reconstructed from the verified C artifact.
