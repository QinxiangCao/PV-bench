# 1027/G — X-mouse in the Campus

*Rating:* 2600 · *Limits:* 1.5s, 256.0 MB · *Tags:* bitmasks, math, number theory

## Description

The campus has $m$ rooms numbered from $0$ to $m - 1$. Also the $x$-mouse lives in the campus. The $x$-mouse is not just a mouse: each second $x$-mouse moves from room $i$ to the room $i \cdot x \mod{m}$ (in fact, it teleports from one room to another since it doesn't visit any intermediate room). Starting position of the $x$-mouse is unknown.

You are responsible to catch the $x$-mouse in the campus, so you are guessing about minimum possible number of traps (one trap in one room) you need to place. You are sure that if the $x$-mouse enters a trapped room, it immediately gets caught.

And the only observation you made is $\text{GCD} (x, m) = 1$.

## Input

The only line contains two integers $m$ and $x$ ($2 \le m \le 10^{14}$, $1 \le x < m$, $\text{GCD} (x, m) = 1$) — the number of rooms and the parameter of $x$-mouse.

## Output

Print the only integer — minimum number of traps you need to install to catch the $x$-mouse.

## Note

In the first example you can, for example, put traps in rooms $0$, $2$, $3$. If the $x$-mouse starts in one of this rooms it will be caught immediately. If $x$-mouse starts in the $1$-st rooms then it will move to the room $3$, where it will be caught.

In the second example you can put one trap in room $0$ and one trap in any other room since $x$-mouse will visit all rooms $1..m-1$ if it will start in any of these rooms.

## Examples

*Example 1 — input:*
```
4 3
```

*Example 1 — output:*
```
3
```

*Example 2 — input:*
```
5 2
```

*Example 2 — output:*
```
2
```
