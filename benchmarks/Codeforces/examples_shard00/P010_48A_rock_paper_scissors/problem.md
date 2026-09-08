# 48/A — Rock-paper-scissors

*Rating:* 900 · *Limits:* 2.0s, 256.0 MB · *Tags:* implementation, schedules

## Description

Uncle Fyodor, Matroskin the Cat and Sharic the Dog live their simple but happy lives in Prostokvashino. Sometimes they receive parcels from Uncle Fyodor’s parents and sometimes from anonymous benefactors, in which case it is hard to determine to which one of them the package has been sent. A photographic rifle is obviously for Sharic who loves hunting and fish is for Matroskin, but for whom was a new video game console meant? Every one of the three friends claimed that the present is for him and nearly quarreled. Uncle Fyodor had an idea how to solve the problem justly: they should suppose that the console was sent to all three of them and play it in turns. Everybody got relieved but then yet another burning problem popped up — who will play first? This time Matroskin came up with a brilliant solution, suggesting the most fair way to find it out: play rock-paper-scissors together. The rules of the game are very simple. On the count of three every player shows a combination with his hand (or paw). The combination corresponds to one of three things: a rock, scissors or paper. Some of the gestures win over some other ones according to well-known rules: the rock breaks the scissors, the scissors cut the paper, and the paper gets wrapped over the stone. Usually there are two players. Yet there are three friends, that’s why they decided to choose the winner like that: If someone shows the gesture that wins over the other two players, then that player wins. Otherwise, another game round is required. Write a program that will determine the winner by the gestures they have shown.

## Input

The first input line contains the name of the gesture that Uncle Fyodor showed, the second line shows which gesture Matroskin showed and the third line shows Sharic’s gesture.

## Output

Print "F" (without quotes) if Uncle Fyodor wins. Print "M" if Matroskin wins and "S" if Sharic wins. If it is impossible to find the winner, print "?".

## Examples

*Example 1 — input:*
```
rock
rock
rock
```

*Example 1 — output:*
```
?
```

*Example 2 — input:*
```
paper
rock
rock
```

*Example 2 — output:*
```
F
```

*Example 3 — input:*
```
scissors
rock
rock
```

*Example 3 — output:*
```
?
```

*Example 4 — input:*
```
scissors
paper
rock
```

*Example 4 — output:*
```
?
```
