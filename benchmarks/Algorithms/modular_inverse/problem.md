# Modular Multiplicative Inverse

## Description

Given coprime positive integers $a$ and $m$, compute the canonical multiplicative inverse of $a$ modulo $m$.

## Input

The function receives $a$ and modulus $m$.

## Output

Return the unique $x$ in $[0,m)$ such that $ax \equiv 1 \pmod m$.

## Constraints

- $1 < m$.
- $0 < a < m$.
- $\gcd(a,m)=1$.

## Source

Classical extended-Euclidean-algorithm problem reconstructed from the verified C artifact.
