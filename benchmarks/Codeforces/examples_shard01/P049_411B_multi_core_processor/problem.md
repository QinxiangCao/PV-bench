# 411/B — Multi-core Processor

*Rating:* 1600 · *Limits:* 1.0s, 256.0 MB · *Tags:* implementation

## Description

The research center Q has developed a new multi-core processor. The processor consists of n cores and has k cells of cache memory. Consider the work of this processor.

At each cycle each core of the processor gets one instruction: either do nothing, or the number of the memory cell (the core will write an information to the cell). After receiving the command, the core executes it immediately. Sometimes it happens that at one cycle, multiple cores try to write the information into a single cell. Unfortunately, the developers did not foresee the possibility of resolving conflicts between cores, so in this case there is a deadlock: all these cores and the corresponding memory cell are locked forever. Each of the locked cores ignores all further commands, and no core in the future will be able to record an information into the locked cell. If any of the cores tries to write an information into some locked cell, it is immediately locked.

The development team wants to explore the deadlock situation. Therefore, they need a program that will simulate the processor for a given set of instructions for each core within m cycles . You're lucky, this interesting work is entrusted to you. According to the instructions, during the m cycles define for each core the number of the cycle, during which it will become locked. It is believed that initially all cores and all memory cells are not locked.

## Input

The first line contains three integers n, m, k (1 ≤ n, m, k ≤ 100). Then follow n lines describing instructions. The i-th line contains m integers: xi1, xi2, ..., xim (0 ≤ xij ≤ k), where xij is the instruction that must be executed by the i-th core at the j-th cycle. If xij equals 0, then the corresponding instruction is «do nothing». But if xij is a number from 1 to k, then the corresponding instruction is «write information to the memory cell number xij».

We assume that the cores are numbered from 1 to n, the work cycles are numbered from 1 to m and the memory cells are numbered from 1 to k.

## Output

Print n lines. In the i-th line print integer ti. This number should be equal to 0 if the i-th core won't be locked, or it should be equal to the number of the cycle when this core will be locked.

## Examples

*Example 1 — input:*
```
4 3 5
1 0 0
1 0 2
2 3 1
3 2 0
```

*Example 1 — output:*
```
1
1
3
0
```

*Example 2 — input:*
```
3 2 2
1 2
1 2
2 2
```

*Example 2 — output:*
```
1
1
0
```

*Example 3 — input:*
```
1 1 1
0
```

*Example 3 — output:*
```
0
```
