# 1063/D — Candies for Children

*Rating:* 2600 · *Limits:* 1.0s, 256.0 MB · *Tags:* brute force, math

## Description

At the children's festival, children were dancing in a circle. When music stopped playing, the children were still standing in a circle. Then Lena remembered, that her parents gave her a candy box with exactly $k$ candies "Wilky May". Lena is not a greedy person, so she decided to present all her candies to her friends in the circle. Lena knows, that some of her friends have a sweet tooth and others do not. Sweet tooth takes out of the box two candies, if the box has at least two candies, and otherwise takes one. The rest of Lena's friends always take exactly one candy from the box.

Before starting to give candies, Lena step out of the circle, after that there were exactly $n$ people remaining there. Lena numbered her friends in a clockwise order with positive integers starting with $1$ in such a way that index $1$ was assigned to her best friend Roma.

Initially, Lena gave the box to the friend with number $l$, after that each friend (starting from friend number $l$) took candies from the box and passed the box to the next friend in clockwise order. The process ended with the friend number $r$ taking the last candy (or two, who knows) and the empty box. Please note that it is possible that some of Lena's friends took candy from the box several times, that is, the box could have gone several full circles before becoming empty.

Lena does not know which of her friends have a sweet tooth, but she is interested in the maximum possible number of friends that can have a sweet tooth. If the situation could not happen, and Lena have been proved wrong in her observations, please tell her about this.

## Input

The only line contains four integers $n$, $l$, $r$ and $k$ ($1 \le n, k \le 10^{11}$, $1 \le l, r \le n$) — the number of children in the circle, the number of friend, who was given a box with candies, the number of friend, who has taken last candy and the initial number of candies in the box respectively.

## Output

Print exactly one integer — the maximum possible number of sweet tooth among the friends of Lena or "-1" (quotes for clarity), if Lena is wrong.

## Note

In the first example, any two friends can be sweet tooths, this way each person will receive the box with candies twice and the last person to take sweets will be the fourth friend.

In the second example, sweet tooths can be any three friends, except for the friend on the third position.

In the third example, only one friend will take candy, but he can still be a sweet tooth, but just not being able to take two candies. All other friends in the circle can be sweet tooths as well, they just will not be able to take a candy even once.

In the fourth example, Lena is wrong and this situation couldn't happen.

## Examples

*Example 1 — input:*
```
4 1 4 12
```

*Example 1 — output:*
```
2
```

*Example 2 — input:*
```
5 3 4 10
```

*Example 2 — output:*
```
3
```

*Example 3 — input:*
```
10 5 5 1
```

*Example 3 — output:*
```
10
```

*Example 4 — input:*
```
5 4 5 6
```

*Example 4 — output:*
```
-1
```
