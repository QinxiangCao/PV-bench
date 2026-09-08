# 1551/C — Interesting Story

*Rating:* 1500 · *Limits:* 4.0s, 256.0 MB · *Tags:* greedy, sortings, strings

## Description

Stephen Queen wants to write a story. He is a very unusual writer, he uses only letters 'a', 'b', 'c', 'd' and 'e'!

To compose a story, Stephen wrote out $n$ words consisting of the first $5$ lowercase letters of the Latin alphabet. He wants to select the maximum number of words to make an interesting story.

Let a story be a sequence of words that are not necessarily different. A story is called interesting if there exists a letter which occurs among all words of the story more times than all other letters together.

For example, the story consisting of three words "bac", "aaada", "e" is interesting (the letter 'a' occurs $5$ times, all other letters occur $4$ times in total). But the story consisting of two words "aba", "abcde" is not (no such letter that it occurs more than all other letters in total).

You are given a sequence of $n$ words consisting of letters 'a', 'b', 'c', 'd' and 'e'. Your task is to choose the maximum number of them to make an interesting story. If there's no way to make a non-empty story, output $0$.

## Input

The first line contains one integer $t$ ($1 \le t \le 5000$) — the number of test cases. Then $t$ test cases follow.

The first line of each test case contains one integer $n$ ($1 \le n \le 2 \cdot 10^5$) — the number of the words in the sequence. Then $n$ lines follow, each of them contains a word — a non-empty string consisting of lowercase letters of the Latin alphabet. The words in the sequence may be non-distinct (i. e. duplicates are allowed). Only the letters 'a', 'b', 'c', 'd' and 'e' may occur in the words.

It is guaranteed that the sum of $n$ over all test cases doesn't exceed $2 \cdot 10^5$; the sum of the lengths of all words over all test cases doesn't exceed $4 \cdot 10^5$.

## Output

For each test case, output the maximum number of words that compose an interesting story. Print 0 if there's no way to make a non-empty interesting story.

## Note

In the first test case of the example, all $3$ words can be used to make an interesting story. The interesting story is "bac aaada e".

In the second test case of the example, the $1$-st and the $3$-rd words can be used to make an interesting story. The interesting story is "aba aba". Stephen can't use all three words at the same time.

In the third test case of the example, Stephen can't make a non-empty interesting story. So the answer is $0$.

In the fourth test case of the example, Stephen can use the $3$-rd and the $4$-th words to make an interesting story. The interesting story is "c bc".

## Examples

*Example 1 — input:*
```
6
3
bac
aaada
e
3
aba
abcde
aba
2
baba
baba
4
ab
ab
c
bc
5
cbdca
d
a
d
e
3
b
c
ca
```

*Example 1 — output:*
```
3
2
0
2
3
2
```
