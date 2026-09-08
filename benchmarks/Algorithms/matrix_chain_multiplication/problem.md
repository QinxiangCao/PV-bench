# Matrix-chain multiplication

## Description

Given the compatible dimension sequence $p_0,p_1,\ldots,p_n$, determine the
minimum number of scalar multiplications needed to compute
$A_0A_1\cdots A_{n-1}$. The matrices themselves need not be multiplied.

For example, dimensions `30 35 15 5 10 20 25` describe six matrices and have
optimal cost `15125`.

## Input

The function receives the matrix dimensions in order and a writable cost table.

## Output

Return the minimum number of scalar multiplications needed for the full chain.

## Constraints

The verification case uses $1\le n\le8$, $1\le p_i\le100$, and a workspace of
$n^2$ integers. These bounds keep every cost at most $7,000,000$.

## Source

Thomas H. Cormen, Charles E. Leiserson, Ronald L. Rivest, and Clifford Stein,
*Introduction to Algorithms*, 4th ed., MIT Press, 2022, Section 14.2
(Section 15.2 in the 3rd edition), "Matrix-chain multiplication."
