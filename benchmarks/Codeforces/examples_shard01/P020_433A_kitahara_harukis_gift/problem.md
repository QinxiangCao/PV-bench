# 433/A — Kitahara Haruki's Gift

*Rating:* 1100 · *Limits:* 1.0s, 256.0 MB · *Tags:* brute force, implementation

## Description

Kitahara Haruki has bought $n$ apples for Touma Kazusa and Ogiso Setsuna. Now he wants to divide all the apples between the friends.

Each apple weights 100 grams or 200 grams. Of course Kitahara Haruki doesn't want to offend any of his friend. Therefore the total weight of the apples given to Touma Kazusa must be equal to the total weight of the apples given to Ogiso Setsuna.

But unfortunately Kitahara Haruki doesn't have a knife right now, so he cannot split any apple into some parts. Please, tell him: is it possible to divide all the apples in a fair way between his friends?

## Input

The first line contains an integer $n$ ($1 \le n \le 100$) — the number of apples. The second line contains $n$ integers $w_1, w_2, \ldots, w_n$ ($w_i = 100$ or $w_i = 200$), where $w_i$ is the weight of the $i$-th apple.

## Output

In a single line print "YES" (without the quotes) if it is possible to divide all the apples between his friends. Otherwise print "NO" (without the quotes).

## Note

In the first test sample Kitahara Haruki can give the first and the last apple to Ogiso Setsuna and the middle apple to Touma Kazusa.

## Examples

*Example 1 — input:*
```
3
100 200 100
```
*Example 1 — output:*
```
YES
```

*Example 2 — input:*
```
4
100 100 100 200
```
*Example 2 — output:*
```
NO
```
