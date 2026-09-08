# 986/A — Fair

*Rating:* 1600 · *Limits:* 2.0s, 512.0 MB · *Tags:* graphs, greedy, number theory, shortest paths

## Description

Some company is going to hold a fair in Byteland. There are $n$ towns in Byteland and $m$ two-way roads between towns. Of course, you can reach any town from any other town using roads.

There are $k$ types of goods produced in Byteland and every town produces only one type. To hold a fair you have to bring at least $s$ different types of goods. It costs $d(u,v)$ coins to bring goods from town $u$ to town $v$ where $d(u,v)$ is the length of the shortest path from $u$ to $v$. Length of a path is the number of roads in this path.

The organizers will cover all travel expenses but they can choose the towns to bring goods from. Now they want to calculate minimum expenses to hold a fair in each of $n$ towns.

## Input

There are $4$ integers $n$, $m$, $k$, $s$ in the first line of input ($1 \le n \le 10^{5}$, $0 \le m \le 10^{5}$, $1 \le s \le k \le min(n, 100)$) — the number of towns, the number of roads, the number of different types of goods, the number of different types of goods necessary to hold a fair.

In the next line there are $n$ integers $a_1, a_2, \ldots, a_n$ ($1 \le a_{i} \le k$), where $a_i$ is the type of goods produced in the $i$-th town. It is guaranteed that all integers between $1$ and $k$ occur at least once among integers $a_{i}$.

In the next $m$ lines roads are described. Each road is described by two integers $u$ $v$ ($1 \le u, v \le n$, $u \ne v$) — the towns connected by this road. It is guaranteed that there is no more than one road between every two towns. It is guaranteed that you can go from any town to any other town via roads.

## Output

Print $n$ numbers, the $i$-th of them is the minimum number of coins you need to spend on travel expenses to hold a fair in town $i$. Separate numbers with spaces.

## Note

Let's look at the first sample.

To hold a fair in town $1$ you can bring goods from towns $1$ ($0$ coins), $2$ ($1$ coin) and $4$ ($1$ coin). Total numbers of coins is $2$.

Town $2$: Goods from towns $2$ ($0$), $1$ ($1$), $3$ ($1$). Sum equals $2$.

Town $3$: Goods from towns $3$ ($0$), $2$ ($1$), $4$ ($1$). Sum equals $2$.

Town $4$: Goods from towns $4$ ($0$), $1$ ($1$), $5$ ($1$). Sum equals $2$.

Town $5$: Goods from towns $5$ ($0$), $4$ ($1$), $3$ ($2$). Sum equals $3$.

## Examples

*Example 1 — input:*
```
5 5 4 3
1 2 4 3 2
1 2
2 3
3 4
4 1
4 5
```

*Example 1 — output:*
```
2 2 2 2 3
```

*Example 2 — input:*
```
7 6 3 2
1 2 3 3 2 2 1
1 2
2 3
3 4
2 5
5 6
6 7
```

*Example 2 — output:*
```
1 1 1 2 2 1 1
```
