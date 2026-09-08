# 1194/C — From S To T

*Rating:* 1300 · *Limits:* 1.0s, 256.0 MB · *Tags:* implementation, strings

## Description

You are given three strings $s$, $t$ and $p$ consisting of lowercase Latin letters. You may perform any number (possibly, zero) operations on these strings.

During each operation you choose any character from $p$, erase it from $p$ and insert it into string $s$ (you may insert this character anywhere you want: in the beginning of $s$, in the end or between any two consecutive characters).

For example, if $p$ is aba, and $s$ is de, then the following outcomes are possible (the character we erase from $p$ and insert into $s$ is highlighted):

- aba $\rightarrow$ ba, de $\rightarrow$ ade;
- aba $\rightarrow$ ba, de $\rightarrow$ dae;
- aba $\rightarrow$ ba, de $\rightarrow$ dea;
- aba $\rightarrow$ aa, de $\rightarrow$ bde;
- aba $\rightarrow$ aa, de $\rightarrow$ dbe;
- aba $\rightarrow$ aa, de $\rightarrow$ deb;
- aba $\rightarrow$ ab, de $\rightarrow$ ade;
- aba $\rightarrow$ ab, de $\rightarrow$ dae;
- aba $\rightarrow$ ab, de $\rightarrow$ dea;

Your goal is to perform several (maybe zero) operations so that $s$ becomes equal to $t$. Please determine whether it is possible.

Note that you have to answer $q$ independent queries.

## Input

The first line contains one integer $q$ ($1 \le q \le 100$) — the number of queries. Each query is represented by three consecutive lines.

The first line of each query contains the string $s$ ($1 \le |s| \le 100$) consisting of lowercase Latin letters.

The second line of each query contains the string $t$ ($1 \le |t| \le 100$) consisting of lowercase Latin letters.

The third line of each query contains the string $p$ ($1 \le |p| \le 100$) consisting of lowercase Latin letters.

## Output

For each query print YES if it is possible to make $s$ equal to $t$, and NO otherwise.

You may print every letter in any case you want (so, for example, the strings yEs, yes, Yes and YES will all be recognized as positive answer).

## Note

In the first test case there is the following sequence of operation:

1. $s = $ ab, $t = $ acxb, $p = $ cax;
2. $s = $ acb, $t = $ acxb, $p = $ ax;
3. $s = $ acxb, $t = $ acxb, $p = $ a.

In the second test case there is the following sequence of operation:

1. $s = $ a, $t = $ aaaa, $p = $ aaabbcc;
2. $s = $ aa, $t = $ aaaa, $p = $ aabbcc;
3. $s = $ aaa, $t = $ aaaa, $p = $ abbcc;
4. $s = $ aaaa, $t = $ aaaa, $p = $ bbcc.

## Examples

*Example 1 — input:*
```
4
ab
acxb
cax
a
aaaa
aaabbcc
a
aaaa
aabbcc
ab
baaa
aaaaa
```

*Example 1 — output:*
```
YES
YES
NO
NO
```
