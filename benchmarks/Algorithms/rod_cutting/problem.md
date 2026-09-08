# Rod cutting

## Description

A rod of integral length $n$ can be cut into integer-length pieces. The array
`price[i]` gives the selling price of one piece of length $i$. Determine the
greatest revenue obtainable by choosing any cuts, including no cut.

## Input

The function receives a rod length $n$, prices for lengths $0$ through $n$, and a writable revenue table.

## Output

Return the maximum revenue obtainable by cutting and selling the rod.

## Constraints

The verification case uses $0\le n\le1000$, `price[0] = 0`, and
$0\le price[i]\le10^6$. It fills `revenue[0..n]`, and its arithmetic
preconditions ensure that every optimum fits in a signed C `int`.

## Source

Thomas H. Cormen, Charles E. Leiserson, Ronald L. Rivest, and Clifford Stein,
*Introduction to Algorithms*, 4th ed., MIT Press, 2022, Section 14.1
(Section 15.1 in the 3rd edition), "Rod cutting."
