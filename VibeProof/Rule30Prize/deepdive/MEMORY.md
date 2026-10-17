# Memory needed to compute c(n)

**Question.** How much memory does it take to compute the center cell c(n) of rule 30, and can the new one-tape technique in OpenAI's preprint [137] push the answer below √n? This is relevant to Problem 3, which is about time; it says nothing about Problem 1.

All of this is analysis on paper, with no computation.

## Baseline

The naive simulation keeps one row of the light cone: about 2n cells, so O(n) bits, in about n² time.

## The CA-native bound: about √n · log n bits

This applies Williams's time-space method (STOC 2025) directly to the light cone, using the Cook–Mertz tree-evaluation algorithm (STOC 2024).

1. **Cut the cone into blocks.** Use time blocks of length b and space blocks of width b. Let node (i, j) be the content of space block j at the end of time block i: b bits.
2. **Each node has three parents.** Information moves at most one cell per step. So the 3b cells of blocks j−1, j, j+1 at the end of time block i−1 determine block j at the end of time block i exactly: run rule 30 for b steps and keep the middle b cells.
3. **The result is a fan-in-3 dependency DAG.** It has height h = n/b and values of b bits.
   - The leaves are the initial row. For a single seed they are trivial.
   - The root is the block holding (n, 0).
4. **Evaluate it with Cook–Mertz.** Tree evaluation works in space about O((h + v) · log v), for height h and value length v. Williams applies this to such DAGs by recomputation. Here that gives O((n/b + b) · log b). With b ≈ √n, the memory is O(√n · log n), and the running time is superpolynomial.

This is a sketch. It is the standard Williams template adapted to a 1D cellular automaton, and I expect it is folklore since his paper. It holds for every 1D cellular automaton of radius 1, not just rule 30.

## Why [137]'s trick does not go below √n here

The paper is "Simulating One-Tape Time in Two-Fifths-Power Space" (openai/math, 2026-09-25). It reaches O(T^{2/5}) for one-tape machines; Williams's bound is √T.

**Its mechanism** (§1, "The mechanism"):
- Partition the tape into blocks of width b.
- With one head, the computation is a sequence of only O(T/b) block visits.
- Between visits only a short controller passes: the state, the head positions and the time, O(log T) bits. All visits to one block can be replayed from that block's initial contents.
- So the history factors over blocks through a small transcript.
- Grouping visits into epochs and rounds of √b, and using interpolation in the Cook–Mertz style, gives Õ(b + (1 + T/b²)·√b). The best choice is b ≈ T^{2/5}.

**The gain comes from the single head.** Only one block is active at a time, and the channel between blocks is narrow. A cellular automaton is the opposite:

- Every cell updates at every step, so every block boundary passes about one bit per step in each direction.
- Over a time span τ, a boundary carries about τ bits, as much as the blocks themselves hold.
- "Factor the history over blocks through a small transcript" has nothing to work with, because the transcript, the boundary columns, is as large as the computation.

**Routing rule 30 through a one-tape machine is worse.** One CA step costs about n tape steps, so T ≈ n² and T^{2/5} ≈ n^{4/5}, more than the CA-native √n.

## Is √n a wall for these methods?

Within block-and-tree-evaluation methods, yes.

- **The interface is a full row segment.** With time blocks of length b, the value passed between consecutive blocks is a row segment of length b. For rule 30 it cannot be compressed: rows have positive entropy and look random.
- **That forces the trade-off.** We need v ≥ b and h ≥ n/b, so h + v ≥ 2√n.
- **Doing better needs a bottleneck.** It would need something like [137]'s narrow channel, a CA-specific reason that little information crosses block boundaries. Rule 30 has information flowing at full rate everywhere.

This is not a lower bound on all algorithms. It is the limit of this family of techniques.

## What it says about the prize problems

- **Problem 3** (is time at least about n?): this gives a clean contrast. Memory compresses to about √n · log n, while the best known time is about n², and Problem 3 conjectures time at least about n. Memory and time behave differently for rule 30.
- **Problem 1**: nothing. Memory upper bounds cannot show non-periodicity.
  - A memory lower bound would: any lower bound above O(log n) bits implies that c is not automatic, so not periodic.
  - Such lower bounds for explicit functions are far beyond current complexity theory. c(n) is computable in time 2^{O(m)} for an m-bit input n, so a bound above linear space in m would separate exponential time from linear space.
