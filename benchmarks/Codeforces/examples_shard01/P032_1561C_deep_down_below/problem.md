# 1561/C — Deep Down Below

*Rating:* 1300 · *Limits:* 1.0s, 256.0 MB · *Tags:* binary search, greedy, sortings

## Description

In a certain video game, the player controls a hero characterized by a single integer value: power. The hero will have to beat monsters that are also characterized by a single integer value: armor.

On the current level, the hero is facing $n$ caves. To pass the level, the hero must enter all the caves in some order, each cave exactly once, and exit every cave safe and sound. When the hero enters cave $i$, he will have to fight $k_i$ monsters in a row: first a monster with armor $a_{i, 1}$, then a monster with armor $a_{i, 2}$ and so on, finally, a monster with armor $a_{i, k_i}$.

The hero can beat a monster if and only if the hero's power is strictly greater than the monster's armor. If the hero can't beat the monster he's fighting, the game ends and the player loses. Note that once the hero enters a cave, he can't exit it before he fights all the monsters in it, strictly in the given order.

Each time the hero beats a monster, the hero's power increases by $1$.

Find the smallest possible power the hero must start the level with to be able to enter all the caves in some order and beat all the monsters.

## Input

Each test contains multiple test cases. The first line contains the number of test cases $t$ ($1 \le t \le 10^5$). Description of the test cases follows.

The first line of each test case contains a single integer $n$ ($1 \le n \le 10^5$) — the number of caves.

The $i$-th of the next $n$ lines contains an integer $k_i$ ($1 \le k_i \le 10^5$) — the number of monsters in the $i$-th cave, followed by $k_i$ integers $a_{i, 1}, a_{i, 2}, \ldots, a_{i, k_i}$ ($1 \le a_{i, j} \le 10^9$) — armor levels of the monsters in cave $i$ in order the hero has to fight them.

It is guaranteed that the sum of $k_i$ over all test cases does not exceed $10^5$.

## Output

For each test case print a single integer — the smallest possible power the hero must start the level with to be able to enter all the caves in some order and beat all the monsters.

## Note

In the first test case, the hero has to beat a single monster with armor $42$, it's enough to have power $43$ to achieve that.

In the second test case, the hero can pass the level with initial power $13$ as follows:

- enter cave $2$: beat a monster with armor $12$, power increases to $14$; beat a monster with armor $11$, power increases to $15$;
- enter cave $1$: beat a monster with armor $10$, power increases to $16$; beat a monster with armor $15$, power increases to $17$; beat a monster with armor $8$, power increases to $18$.

## Examples

*Example 1 — input:*
```
2
1
1 42
2
3 10 15 8
2 12 11
```
*Example 1 — output:*
```
43
13
```
