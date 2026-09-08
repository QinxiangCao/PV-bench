# 707/A — Brain's Photos

*Rating:* 800 · *Limits:* 2.0s, 256.0 MB · *Tags:* implementation

## Description

Small, but very brave, mouse Brain was not accepted to summer school of young villains. He was upset and decided to postpone his plans of taking over the world, but to become a photographer instead.

As you may know, the coolest photos are on the film (because you can specify the hashtag #film for such).

Brain took a lot of colourful pictures on colored and black-and-white film. Then he developed and translated it into a digital form. But now, color and black-and-white photos are in one folder, and to sort them, one needs to spend more than one hour!

As soon as Brain is a photographer not programmer now, he asks you to help him determine for a single photo whether it is colored or black-and-white.

Photo can be represented as a matrix sized n × m, and each element of the matrix stores a symbol indicating corresponding pixel color. There are only 6 colors:

- 'C' (cyan)
- 'M' (magenta)
- 'Y' (yellow)
- 'W' (white)
- 'G' (grey)
- 'B' (black)

The photo is considered black-and-white if it has only white, black and grey pixels in it. If there are any of cyan, magenta or yellow pixels in the photo then it is considered colored.

## Input

The first line of the input contains two integers n and m (1 ≤ n, m ≤ 100) — the number of photo pixel matrix rows and columns respectively.

Then n lines describing matrix rows follow. Each of them contains m space-separated characters describing colors of pixels in a row. Each character in the line is one of the 'C', 'M', 'Y', 'W', 'G' or 'B'.

## Output

Print the "#Black&White" (without quotes), if the photo is black-and-white and "#Color" (without quotes), if it is colored, in the only line.

## Examples

*Example 1 — input:*
```
2 2
C M
Y Y
```
*Example 1 — output:*
```
#Color
```

*Example 2 — input:*
```
3 2
W W
W W
B B
```
*Example 2 — output:*
```
#Black&White
```

*Example 3 — input:*
```
1 1
W
```
*Example 3 — output:*
```
#Black&White
```
