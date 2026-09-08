# P1220 Turning Off Streetlights

## Description

$n$ streetlights lie on a road in increasing position order. Each has a power
rating. A worker begins at light $c$, immediately turns it off, and then walks
at one metre per second to turn off the others. Switching time is negligible.
Minimize the energy consumed by all lights from the start until every light is
off.

## Input

The input gives the number of lights, the starting light, and every light's position and power consumption.

## Output

Print the minimum total energy consumed while all lights are turned off.

## Constraints

- $1 \le n \le 50$ and $1 \le c \le n$.
- Positions are strictly increasing; the original positions are in $[1,100]$.
- $1 \le W_i \le 100$.

## Source

[Luogu P1220, "Turning Off Streetlights"](https://www.luogu.com.cn/problem/P1220).
