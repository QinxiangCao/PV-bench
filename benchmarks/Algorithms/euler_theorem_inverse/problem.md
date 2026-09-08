# Modular Inverse by Euler's Theorem

## Description

For coprime positive integers `value` and `modulus`, compute the canonical multiplicative inverse of `value` modulo `modulus` using Euler's theorem.

## Input

The function receives `value` and `modulus`.

## Output

Return the unique integer $x$ in $[0,modulus)$ satisfying $value \cdot x \equiv 1 \pmod{modulus}$.

## Constraints

- $0 < value < modulus$.
- $2 \le modulus \le 46341$.
- $\gcd(value,modulus)=1$.

## Source

Classical number-theory problem reconstructed from the verified C artifact.
