# 985/A — Chess Placing

*Rating:* 1100 · *Limits:* 1.0s, 256.0 MB · *Tags:* implementation

## Description

You are given a chessboard of size 1 × n. It is guaranteed that n is even. The chessboard is painted like this: "BWBW...BW".

Some cells of the board are occupied by the chess pieces. Each cell contains no more than one chess piece. It is known that the total number of pieces equals to $$\frac{\pi}{2}$$.

In one step you can move one of the pieces one cell to the left or to the right. You cannot move pieces beyond the borders of the board. You also cannot move pieces to the cells that are already occupied.

Your task is to place all the pieces in the cells of the same color using the minimum number of moves (all the pieces must occupy only the black cells or only the white cells after all the moves are made).

## Input

The first line of the input contains one integer n (2 ≤ n ≤ 100, n is even) — the size of the chessboard.

The second line of the input contains $$\frac{\pi}{2}$$ integer numbers $${ \hat { p } } _ { 1 }, { \hat { p } } _ { 2 }, \ldots, { \hat { p } } _ { \frac { n } { 2 } }$$ (1 ≤ pi ≤ n) — initial positions of the pieces. It is guaranteed that all the positions are distinct.

## Output

Print one integer — the minimum number of moves you have to make to place all the pieces in the cells of the same color.

## Note

In the first example the only possible strategy is to move the piece at the position 6 to the position 5 and move the piece at the position 2 to the position 3. Notice that if you decide to place the pieces in the white cells the minimum number of moves will be 3.

In the second example the possible strategy is to move $$5 \rightarrow 9$$ in 4 moves, then $$4 \rightarrow 7$$ in 3 moves, $$3 \rightarrow 5$$ in 2 moves and $$2\rightarrow3$$ in 1 move.

## Examples

*Example 1 — input:*
```
6
1 2 6
```

*Example 1 — output:*
```
2
```

*Example 2 — input:*
```
10
1 2 3 4 5
```

*Example 2 — output:*
```
10
```
