# 639/D — Bear and Contribution

*Rating:* 2400 · *Limits:* 4.0s, 256.0 MB · *Tags:* data structures, greedy, sortings, two pointers

## Description

Codeforces is a wonderful platform and one its feature shows how much someone contributes to the community. Every registered user has contribution — an integer number, not necessarily positive. There are n registered users and the i-th of them has contribution ti.

Limak is a little polar bear and he's new into competitive programming. He doesn't even have an account in Codeforces but he is able to upvote existing blogs and comments. We assume that every registered user has infinitely many blogs and comments.

- Limak can spend b minutes to read one blog and upvote it. Author's contribution will be increased by 5.
- Limak can spend c minutes to read one comment and upvote it. Author's contribution will be increased by 1.

Note that it's possible that Limak reads blogs faster than comments.

Limak likes ties. He thinks it would be awesome to see a tie between at least k registered users. To make it happen he is going to spend some time on reading and upvoting. After that, there should exist an integer value x that at least k registered users have contribution exactly x.

How much time does Limak need to achieve his goal?

## Input

The first line contains four integers n, k, b and c (2 ≤ k ≤ n ≤ 200 000, 1 ≤ b, c ≤ 1000) — the number of registered users, the required minimum number of users with the same contribution, time needed to read and upvote a blog, and time needed to read and upvote a comment, respectively.

The second line contains n integers t1, t2, ..., tn (|ti| ≤ 109) where ti denotes contribution of the i-th registered user.

## Output

Print the minimum number of minutes Limak will spend to get a tie between at least k registered users.

## Note

In the first sample, there are 4 registered users and Limak wants a tie between at least 3 of them. Limak should behave as follows.

- He spends 100 minutes to read one blog of the 4-th user and increase his contribution from 1 to 6.
- Then he spends 4·30 = 120 minutes to read four comments of the 2-nd user and increase his contribution from 2 to 6 (four times it was increaded by 1).

In the given scenario, Limak spends 100 + 4·30 = 220 minutes and after that each of users 2, 3, 4 has contribution 6.

In the second sample, Limak needs 30 minutes to read a blog and 100 minutes to read a comment. This time he can get 3 users with contribution equal to 12 by spending 100 + 3·30 = 190 minutes:

- Spend 2·30 = 60 minutes to read two blogs of the 1-st user to increase his contribution from 2 to 12.
- Spend 30 + 100 minutes to read one blog and one comment of the 3-rd user. His contribution will change from 6 to 6 + 5 + 1 = 12.

## Examples

*Example 1 — input:*
```
4 3 100 30
12 2 6 1
```

*Example 1 — output:*
```
220
```

*Example 2 — input:*
```
4 3 30 100
12 2 6 1
```

*Example 2 — output:*
```
190
```

*Example 3 — input:*
```
6 2 987 789
-8 42 -4 -65 -8 -8
```

*Example 3 — output:*
```
0
```
