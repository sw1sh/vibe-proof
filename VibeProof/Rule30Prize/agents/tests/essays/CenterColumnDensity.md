---
Template: ComputationalEssay
Name: How Often the Center Column of Rule 30 Is Black
Author: A test submission
Date: 2026
Description: A short computational essay on Problem 2 of the Rule 30 Prize, without a Lean proof: how close the fraction of black cells in rule 30's center column stays to one half over its first 100,000 steps
Abstract: Problem 2 of the Rule 30 Prize asks whether black and white cells occur equally often, on average, in the center column of rule 30. This essay computes the first 100,000 cells of the column and the running fraction of black ones. Scaled the way a random sequence's fluctuations are, the distance from one half stays of order one. The numbers agree with one half, but they prove nothing about the limit, and the essay makes no formal claim. It is a test submission of an essay without Lean.
Keywords: [rule 30, center column, density, Rule 30 Prize, computational essay]
Sources: ["[Announcing the Rule 30 Prizes](https://writings.stephenwolfram.com/2019/10/announcing-the-rule-30-prizes/)"]
---

## The question

Rule 30 updates every cell from itself and its two neighbors: the new color is *left* XOR (*center* OR *right*). Started from a single black cell, its center column looks random. Problem 2 of the Rule 30 Prize asks whether each color occurs, on average, equally often in that column.

## The center column

The first 100,000 cells of the center column, 1 for black:

```wl
column = CellularAutomaton[30, {{1}, 0}, {10^5 - 1, {{0}}}];
{Length[column], Take[column, 30]}
```

## The running fraction of black cells

The fraction of black cells among the first $n$, for every $n$ up to 100,000:

```wl
density = N[Accumulate[column]/Range[Length[column]]];
ListLogLinearPlot[Transpose[{Range[1, 10^5, 25], density[[1 ;; ;; 25]]}],
    PlotRange -> {0.4, 0.6}, GridLines -> {None, {0.5}}, AxesLabel -> {"n", "fraction black"}, ImageSize -> Medium]
```

After the first few hundred steps, the fraction stays close to one half.

## How far from one half

For a random sequence of fair coin flips, the fraction of heads strays from one half by about $1/(2\sqrt{n})$. Multiplied by $2\sqrt{n}$, the distance should stay of order one:

```wl
scaled = 2 Sqrt[N[Range[Length[column]]]] (density - 1/2);
ListLogLinearPlot[Transpose[{Range[1, 10^5, 25], scaled[[1 ;; ;; 25]]}],
    PlotRange -> {-3, 3}, GridLines -> {None, {-2, 0, 2}}, AxesLabel -> {"n", "scaled distance"}, ImageSize -> Medium]
```

The largest scaled distance past the first thousand steps, and the last one:

```wl
{Max[Abs[scaled[[1000 ;;]]]], Last[scaled]}
```

## What this does not show

These are 100,000 cells of an infinite column. Agreement with one half and with random fluctuations, however long it lasts, proves nothing about the limit that Problem 2 asks about. This essay has no Lean proof and claims no theorem.
