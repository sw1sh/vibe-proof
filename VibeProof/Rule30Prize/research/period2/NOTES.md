# period2: coordinator searches for eventual period 2

These are the coordinator's searches for a left half that would allow an eventual period 2. If the center alternates from time T, column -1 must be black at every black time of the center. The scripts search for finite left halves of width W that keep this up. All of them die. This is computational evidence only; Q01 is proved in Lean only up to width 52, or 56 in `research/kernel-certify-r2`.

- **Round 1** (05:19–05:30, 2026-10-15): `fiber2.py`, `search2.py`, `search2_free.py`, `death_free.py`, `deathdepth.py`, `crosscheck.py`, `weights.py`.
  - Every constrained left half of width W ≤ 39 dies, within about 1.25W–2W steps.
  - The free bits are column -1 at white times. They determine the starting row through a triangular map, with a pivot at every other depth. BRIEF2.md records this.
- **After round 2** (09:43): `search_lang.py`.
  - It imposes the right half's empirical block law as well: column 1 at white times lies in {10000, 100}*, and 100 never occurs twice in a row. Round 2's synthesis measured this law in `synth-r2`; it is empirical, not proved.
  - Under this law, the left search still dies for every W ≤ 196.
  - Survivors grow by about 1.05× per unit of width, and the excess D(W) − W grows slowly, from about 2 to 18.
  - This run's output was not saved; the figures come from the coordinator's record of the session.
