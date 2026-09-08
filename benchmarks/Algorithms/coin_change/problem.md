# Maximum Reachable Amount

## Description

Given zero or more positive coin denominations and a nonnegative target bound
`amount`, return the greatest reachable amount that does not exceed `amount`.
There is no requirement to reach `amount` exactly. If no positive amount at
most `amount` is reachable, return `0`.

Each denomination is reusable without limit. Duplicate denominations, if
present, do not change which amounts are reachable.

## Input

The function receives `coins`, `coinsSize`, `amount`, and an uninitialized workspace `dp[0..amount]`.

## Output

Return the greatest reachable amount not exceeding `amount`; the function also fills the reachability table `dp`.

## Constraints

- $0 \le \texttt{coinsSize} \le 100000$.
- $0 \le \texttt{amount} \le 100000$.
- $1 \le \texttt{coins[i]} \le \texttt{INT\_MAX}$ for every valid index.
- `coins` contains exactly `coinsSize` integers.
- `dp` contains exactly `amount + 1` writable integers.

The implementation runs in $O(\texttt{coinsSize}\times\texttt{amount})$ time
and uses $O(\texttt{amount})$ caller-provided workspace.

## Source

Adapted as a reachability variant from
[LeetCode 322, "Coin Change"](https://leetcode.com/problems/coin-change/).
