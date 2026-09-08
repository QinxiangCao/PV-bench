# 474/B — Worms

*Rating:* 1200 · *Limits:* 1.0s, 256.0 MB · *Tags:* binary search, implementation

## Description

It is lunch time for Mole. His friend, Marmot, prepared him a nice game for lunch.

Marmot brought Mole $n$ ordered piles of worms such that $i$-th pile contains $a_i$ worms. He labeled all these worms with consecutive integers: worms in first pile are labeled with numbers $1$ to $a_1$, worms in second pile are labeled with numbers $a_1 + 1$ to $a_1 + a_2$ and so on. See the example for a better understanding.

Mole can't eat all the worms (Marmot brought a lot) and, as we all know, Mole is blind, so Marmot tells him the labels of the best juicy worms. Marmot will only give Mole a worm if Mole says correctly in which pile this worm is contained.

Poor Mole asks for your help. For all juicy worms said by Marmot, tell Mole the correct answers.

## Input

The first line contains a single integer $n$ ($1 \le n \le 10^5$), the number of piles.

The second line contains $n$ integers $a_1, a_2, \ldots, a_n$ ($1 \le a_i \le 10^3$, $a_1 + a_2 + \ldots + a_n \le 10^6$), where $a_i$ is the number of worms in the $i$-th pile.

The third line contains single integer $m$ ($1 \le m \le 10^5$), the number of juicy worms said by Marmot.

The fourth line contains $m$ integers $q_1, q_2, \ldots, q_m$ ($1 \le q_i \le a_1 + a_2 + \ldots + a_n$), the labels of the juicy worms.

## Output

Print $m$ lines to the standard output. The $i$-th line should contain an integer, representing the number of the pile where the worm labeled with the number $q_i$ is.

## Note

For the sample input:

- The worms with labels from $[1, 2]$ are in the first pile.
- The worms with labels from $[3, 9]$ are in the second pile.
- The worms with labels from $[10, 12]$ are in the third pile.
- The worms with labels from $[13, 16]$ are in the fourth pile.
- The worms with labels from $[17, 25]$ are in the fifth pile.

## Examples

*Example 1 — input:*
```
5
2 7 3 4 9
3
1 25 11
```
*Example 1 — output:*
```
1
5
3
```
