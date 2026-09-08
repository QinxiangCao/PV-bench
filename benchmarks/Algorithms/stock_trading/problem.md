# P2569 Stock Trading

## Description

For each of the next $T$ days, the buy price, sell price, maximum purchasable
shares, and maximum sellable shares are known. Any two transaction days must
have at least $W$ complete days between them, and holdings may never exceed
`MaxP`. Starting with no shares and unlimited cash, maximize the profit earned
over the $T$ days.

## Input

The input gives the number of days, stock limit, waiting period, and each day's prices and transaction limits.

## Output

Print the maximum achievable profit.

## Constraints

- $0 \le W < T \le 2000$ and $1 \le \mathrm{MaxP} \le 2000$.
- $1 \le BP_i \le AP_i \le 1000$.
- $1 \le AS_i,BS_i \le \mathrm{MaxP}$.
- The verification case uses reduced bounds $T,\mathrm{MaxP}\le990$.

## Source

[Luogu P2569, SCOI 2010](https://www.luogu.com.cn/problem/P2569?lang=en).
