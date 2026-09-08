# 555/A — Case of Matryoshkas

*Rating:* 1500 · *Limits:* 2.0s, 256.0 MB · *Tags:* implementation

## Description

Andrewid the Android is a galaxy-famous detective. He is now investigating the case of vandalism at the exhibition of contemporary art.

The main exhibit is a construction of n matryoshka dolls that can be nested one into another. The matryoshka dolls are numbered from 1 to n. A matryoshka with a smaller number can be nested in a matryoshka with a higher number, two matryoshkas can not be directly nested in the same doll, but there may be chain nestings, for example, 1 → 2 → 4 → 5.

In one second, you can perform one of the two following operations:

- Having a matryoshka a that isn't nested in any other matryoshka and a matryoshka b, such that b doesn't contain any other matryoshka and is not nested in any other matryoshka, you may put a in b;
- Having a matryoshka a directly contained in matryoshka b, such that b is not nested in any other matryoshka, you may get a out of b.

According to the modern aesthetic norms the matryoshka dolls on display were assembled in a specific configuration, i.e. as several separate chains of nested matryoshkas, but the criminal, following the mysterious plan, took out all the dolls and assembled them into a single large chain (1 → 2 → ... → n). In order to continue the investigation Andrewid needs to know in what minimum time it is possible to perform this action.

## Input

The first line contains integers n ($1 \le n \le 10^5$) and $k$ ($1 \le k \le 10^5$) — the number of matryoshkas and matryoshka chains in the initial configuration.

The next k lines contain the descriptions of the chains: the i-th line first contains number mi (1 ≤ mi ≤ n), and then mi numbers ai1, ai2, ..., aimi — the numbers of matryoshkas in the chain (matryoshka ai1 is nested into matryoshka ai2, that is nested into matryoshka ai3, and so on till the matryoshka aimi that isn't nested into any other matryoshka).

It is guaranteed that m1 + m2 + ... + mk = n, the numbers of matryoshkas in all the chains are distinct, in each chain the numbers of matryoshkas follow in the ascending order.

## Output

In the single line print the minimum number of seconds needed to assemble one large chain from the initial configuration.

## Note

In the first sample test there are two chains: 1 → 2 and 3. In one second you can nest the first chain into the second one and get 1 → 2 → 3.

In the second sample test you need to disassemble all the three chains into individual matryoshkas in 2 + 1 + 1 = 4 seconds and then assemble one big chain in 6 seconds.

## Examples

*Example 1 — input:*
```
3 2
2 1 2
1 3
```

*Example 1 — output:*
```
1
```

*Example 2 — input:*
```
7 3
3 1 3 7
2 2 5
2 4 6
```

*Example 2 — output:*
```
10
```
