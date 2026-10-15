import Ruliology.CellularAutomata.Rule30Diagonals
import Ruliology.CellularAutomata.Rule30Window

/-!
# The periods of the right diagonals of rule 30

`R j t = cell t (t - j)` is the `j`-th diagonal from the right edge; `R_periodic` says it repeats
with period `2^j`. Here we pin the periods down much further. Write `Per j p` for "`R j` repeats
with period `p`", and `e_j` for the least `k` with `Per j (2^k)`.

* `halve`, `per_mono_all`: if `R (j+1)` has period `2^k`, so has every `R i`, `i ≤ j`
  (`e_0 ≤ e_1 ≤ e_2 ≤ …`). The proof descends from a white light-cone triangle that diagonal
  `j + 1` repeats at time `2^k`: two white diagonals force the two before them white.
* `per_step`: if `R j` has period `2^k`, `R (j+1)` has period `2^(k+1)`  (`e_{j+1} ≤ e_j + 1`).
* `shift_formula`, `per_succ_iff`, `antiperiod`: if `R j` has period `2^k`, then
  `R (j+1) (t + 2^k) = R (j+1) t xor R (j+1) (2^k)`. So `e_{j+1} = e_j + [R (j+1) (2^{e_j})]`: the
  period doubles exactly when the cell at time `2^{e_j}` on the next diagonal is black, and then
  the diagonal is complemented by a shift of half its period.
* `per_iff_gap`: `R n` has period `2^k` iff row `2^k` has `n` white cells left of its right edge.
* `zero_gap`, `zero_gap_cell`: with `J` the last diagonal of period `2^k`, every row `N = 2^k u`
  with `u` odd reads `1 0^J 1` leftwards from its right edge.
* `last_one`: the last cell of every period is black, so row `2^k - 1` ends in `J + 1` black cells.
* `restart`, `center_restart`, `column_continuity`: the pattern restarts at the right edge; column
  `2^k u` repeats `c(0), …, c(J)`, and columns `p`, `p + 2^k u` agree `s` steps after their birth
  whenever `R s` has period `2^k`.
* `center_black_lt`: a black center cell `c(t)` lies in the first period of its diagonal.
* `no_three`: the period never doubles three times in a row.
* `not_per_small`, `per_upper`: `j < 2^(e_j + 1)` and `e_j ≤ (2j + 1)/3`.
* `per_14`, `per_23`, `not_half_lower`: `e_14 ≤ 6` and `e_23 ≤ 8` (kernel computation of rows
  `64` and `256`), so `e_j ≥ ⌊j/2⌋` is false.
-/

namespace Ruliology.CellularAutomata
namespace Rule30RightPeriods

open Rule30Jen Rule30Diagonals

/-! ### Basic facts -/

theorem R_congr {j j' t t' : Nat} (hj : j = j') (ht : t = t') : R j t = R j' t' := by
  subst hj ht; rfl

/-- Outside the light cone the diagonal is white. -/
theorem R_lt {j t : Nat} (h : 2 * t < j) : R j t = false :=
  cell_eq_false_of_lt t _ (by omega)

theorem R_init {j : Nat} (h : 1 ≤ j) : R j 0 = false := R_lt (by omega)

/-- The left edge (or its right neighbour) is black where diagonal `j ≥ 1` enters the light cone. -/
theorem R_half {j : Nat} (h : 1 ≤ j) : R j ((j + 1) / 2) = true := by
  obtain ⟨s, hs⟩ : ∃ s, j = 2 * s ∨ j = 2 * s + 1 := ⟨j / 2, by omega⟩
  rcases hs with rfl | rfl
  · show cell ((2 * s + 1) / 2) ((((2 * s + 1) / 2 : Nat) : Int) - ((2 * s : Nat) : Int)) = true
    rw [show (2 * s + 1) / 2 = s by omega,
      cell_congr (show ((s : Nat) : Int) - ((2 * s : Nat) : Int) = -(s : Int) by omega)]
    exact cell_left_edge s
  · show cell ((2 * s + 1 + 1) / 2) ((((2 * s + 1 + 1) / 2 : Nat) : Int) - ((2 * s + 1 : Nat) : Int))
      = true
    rw [show (2 * s + 1 + 1) / 2 = s + 1 by omega,
      cell_congr (show (((s + 1 : Nat)) : Int) - ((2 * s + 1 : Nat) : Int)
        = ((1 : Nat) : Int) - ((s + 1 : Nat) : Int) by omega)]
    exact D_one s

theorem R_step' {a b c t : Nat} (hb : b = a + 1) (hc : c = a + 2) :
    R c (t + 1) = xor (R c t) (R b t || R a t) := by
  subst hb hc; exact R_step a t

theorem R_one_eq : ∀ t, R 1 t = (t % 2 == 1)
  | 0 => R_init (by omega)
  | t + 1 => by
    rw [R_one_succ, R_one_eq t]
    rcases Nat.mod_two_eq_zero_or_one t with h | h
    · have h' : (t + 1) % 2 = 1 := by omega
      simp [h, h']
    · have h' : (t + 1) % 2 = 0 := by omega
      simp [h, h']

theorem R_two_eq_one : ∀ t, R 2 t = R 1 t
  | 0 => by rw [R_init (by omega), R_init (by omega)]
  | t + 1 => by
    rw [R_step' (a := 0) (b := 1) (c := 2) rfl rfl, R_one_succ, R_zero, R_two_eq_one t]
    cases R 1 t <;> rfl

/-! ### Periods -/

/-- `R j` repeats with period `p`. -/
def Per (j p : Nat) : Prop := ∀ t, R j (t + p) = R j t

theorem Per.mul {j p : Nat} (h : Per j p) : ∀ n, Per j (n * p)
  | 0 => fun t => by simp
  | n + 1 => fun t => by
    rw [show t + (n + 1) * p = (t + n * p) + p by rw [Nat.succ_mul]; omega, h, Per.mul h n t]

theorem Per.pow_mono {j a b : Nat} (h : Per j (2 ^ a)) (hab : a ≤ b) : Per j (2 ^ b) := by
  have := h.mul (2 ^ (b - a))
  rwa [← Nat.pow_add, show b - a + a = b by omega] at this

theorem per_zero (p : Nat) : Per 0 p := fun t => by rw [R_zero, R_zero]

theorem per_one (k : Nat) : Per 1 (2 ^ (k + 1)) := fun t => by
  rw [R_one_eq, R_one_eq, Nat.pow_succ]
  have : (t + 2 ^ k * 2) % 2 = t % 2 := by omega
  rw [this]

theorem per_R_periodic (j : Nat) : Per j (2 ^ j) := R_periodic j

/-- A sequence periodic with period `p` and equal to `b` at `0` equals `b` at every multiple of
`p`. -/
theorem Per.at_mul {j p : Nat} (h : Per j p) (n : Nat) : R j (p * n) = R j 0 := by
  have := h.mul n 0
  rwa [Nat.zero_add, Nat.mul_comm] at this

/-- An eventually-white diagonal is impossible: a diagonal `j ≥ 1` with period `1` is constant,
hence white, but it meets the left edge. -/
theorem not_per_one {j : Nat} (hj : 1 ≤ j) : ¬ Per j 1 := by
  intro h
  have hc : ∀ t, R j t = false := by
    intro t
    induction t with
    | zero => exact R_init hj
    | succ t ih => rw [h t, ih]
  have := R_half hj
  rw [hc] at this
  exact absurd this (by decide)

/-! ### Accumulation -/

/-- A sequence that accumulates a `L`-periodic input shifts by a constant over `L` steps. -/
theorem accum_shift {x g : Nat → Bool} {L : Nat} (hx : ∀ t, x (t + 1) = xor (x t) (g t))
    (hg : ∀ t, g (t + L) = g t) : ∀ t, x (t + L) = xor (x t) (xor (x L) (x 0)) := by
  have hconst : ∀ t, xor (x (t + L)) (x t) = xor (x L) (x 0) := by
    intro t
    induction t with
    | zero => rw [Nat.zero_add]
    | succ t ih =>
      rw [show t + 1 + L = (t + L) + 1 by omega, hx (t + L), hx t, hg t, ← ih]
      cases x (t + L) <;> cases x t <;> cases g t <;> rfl
  intro t
  have h := hconst t
  revert h
  cases x (t + L) <;> cases x t <;> cases xor (x L) (x 0) <;> simp

/-! ### The halving lemma -/

/-- Diagonals `a` and `a + 1` are white at times `H + t`, `t < M`. -/
def Z (H a M : Nat) : Prop := ∀ t, t < M → R a (H + t) = false ∧ R (a + 1) (H + t) = false

/-- Two white diagonals force the two before them to be white one step less long: the `or` in
`R (a+3) (s+1) = R (a+3) s xor (R (a+2) s || R (a+1) s)` is false only if both inputs are. -/
theorem Z_down {H a M : Nat} (h : Z H (a + 2) (M + 1)) : Z H a M := by
  intro t ht
  obtain ⟨h2, h3⟩ := h t (by omega)
  obtain ⟨h2', h3'⟩ := h (t + 1) (by omega)
  have s3 := R_step' (a := a + 1) (b := a + 2) (c := a + 2 + 1) (t := H + t) (by omega) (by omega)
  have s2 := R_step' (a := a) (b := a + 1) (c := a + 2) (t := H + t) rfl rfl
  rw [show H + t + 1 = H + (t + 1) by omega] at s3 s2
  rw [h3', h3, h2] at s3
  rw [h2', h2] at s2
  constructor
  · revert s2; cases R (a + 1) (H + t) <;> cases R a (H + t) <;> simp
  · revert s3; cases R (a + 1) (H + t) <;> simp

theorem Z_iter {H a M : Nat} : ∀ s, Z H (a + 2 * s) (M + s) → Z H a M
  | 0, h => by simpa using h
  | s + 1, h => by
    have h' : Z H ((a + 2) + 2 * s) ((M + 1) + s) := by
      rw [show (a + 2) + 2 * s = a + 2 * (s + 1) by omega,
        show (M + 1) + s = M + (s + 1) by omega]
      exact h
    exact Z_down (Z_iter s h')

theorem Z_mono {H a M M' : Nat} (h : Z H a M) (hM : M' ≤ M) : Z H a M' :=
  fun t ht => h t (by omega)

/-- **Monotonicity lemma.** Let `j ≥ 2` and `H = 1` or `H` even. If diagonal `j + 1` repeats with
period `H`, then so do all diagonals `0, …, j`.

Otherwise take the first diagonal `i` without period `H`. Its input has period `H`, so a shift by
`H` adds a constant to it, which must be `1`: the diagonal is black at time `H`. But diagonal
`j + 1` repeats at time `H` the white light-cone triangle of time `0`, which makes diagonals `j`
and `j - 1` white for a while after `H`; two white diagonals force the two before them white
(`Z_down`), and descending to diagonal `i` makes it white at time `H`. -/
theorem halve {j H : Nat} (hj : 2 ≤ j) (hH : H = 1 ∨ H % 2 = 0) (h1 : Per (j + 1) H) :
    ∀ i, i ≤ j → Per i H := by
  -- diagonals `j - 1` and `j` are white at times `H + t`, `t < j / 2`
  have hZ : Z H (j - 1) (j / 2) := by
    intro t ht
    have s := R_step' (a := j - 1) (b := j) (c := j + 1) (t := H + t) (by omega) (by omega)
    rw [show H + t + 1 = (t + 1) + H by omega, h1, show H + t = t + H by omega, h1,
      R_lt (show 2 * (t + 1) < j + 1 by omega), R_lt (show 2 * t < j + 1 by omega)] at s
    rw [show t + H = H + t by omega] at s
    rw [show j - 1 + 1 = j by omega]
    revert s; cases R j (H + t) <;> cases R (j - 1) (H + t) <;> simp
  intro i
  induction i using Nat.strongRecOn with
  | _ i ih =>
  intro hi
  match i, ih, hi with
  | 0, _, _ => exact per_zero H
  | 1, _, _ =>
    rcases hH with rfl | hH
    · exact absurd h1 (not_per_one (by omega))
    · obtain ⟨k, rfl⟩ : ∃ k, H = 2 * k := ⟨H / 2, by omega⟩
      intro t
      rw [R_one_eq, R_one_eq, show (t + 2 * k) % 2 = t % 2 by omega]
  | 2, ih, _ =>
    have p1 := ih 1 (by omega) (by omega)
    intro t; rw [R_two_eq_one, R_two_eq_one, p1]
  | m + 3, ih, hi =>
    have pa := ih (m + 1) (by omega) (by omega)
    have pb := ih (m + 2) (by omega) (by omega)
    have sh := accum_shift (x := R (m + 3)) (g := fun t => R (m + 2) t || R (m + 1) t) (L := H)
      (fun t => R_step' (by omega) (by omega)) (fun t => by simp only; rw [pa, pb])
    rw [R_init (show 1 ≤ m + 3 by omega)] at sh
    cases hH' : R (m + 3) H
    · intro t; rw [sh t, hH']; cases R (m + 3) t <;> rfl
    · -- the diagonal is black at time `H`: descend from `j - 1, j` to reach it white
      exfalso
      let s := (j - m - 3) / 2
      let a := j - 1 - 2 * s
      have hz : Z H (a + 2 * s) (1 + s) := by
        rw [show a + 2 * s = j - 1 by omega]
        exact Z_mono hZ (by omega)
      have := (Z_iter s hz) 0 (by omega)
      rw [Nat.add_zero] at this
      rcases (show a = m + 2 ∨ a = m + 3 by omega) with ha | ha
      · rw [show a + 1 = m + 3 by omega, hH'] at this
        exact absurd this.2 (by decide)
      · rw [ha, hH'] at this
        exact absurd this.1 (by decide)

/-! ### The main structure theorems -/

/-- **Monotonicity**: if diagonal `j + 1` repeats with period `2^k`, so do all diagonals up to `j`.
So `e_j ≤ e_{j+1}`. -/
theorem per_mono_all {j k : Nat} (h : Per (j + 1) (2 ^ k)) : ∀ i, i ≤ j → Per i (2 ^ k) := by
  rcases (show j = 0 ∨ j = 1 ∨ 2 ≤ j by omega) with rfl | rfl | hj
  · intro i hi
    rw [show i = 0 by omega]; exact per_zero _
  · intro i hi
    rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl
    · exact per_zero _
    · intro t; rw [← R_two_eq_one, ← R_two_eq_one]; exact h t
  · apply halve hj _ h
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · left; rw [h0]
    · right
      obtain ⟨m, hm⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
      rw [hm, Nat.pow_succ]; omega

theorem per_mono {j k : Nat} (h : Per (j + 1) (2 ^ k)) : Per j (2 ^ k) :=
  per_mono_all h j (Nat.le_refl j)

theorem per_mono_le {i j k : Nat} (hij : i ≤ j) (h : Per j (2 ^ k)) : Per i (2 ^ k) := by
  rcases Nat.eq_or_lt_of_le hij with rfl | hlt
  · exact h
  · obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    exact per_mono_all h i (by omega)

/-- The input of diagonal `j + 2` repeats with the period of diagonal `j + 1`. -/
theorem input_per {j k : Nat} (h : Per (j + 1) (2 ^ k)) :
    ∀ t, (R (j + 1) (t + 2 ^ k) || R j (t + 2 ^ k)) = (R (j + 1) t || R j t) := by
  intro t; rw [h t, per_mono h t]

/-- **Shift formula**: if diagonal `j` repeats with period `2^k`, a shift of `2^k` adds the
constant `R (j+1) (2^k)` to diagonal `j + 1`. -/
theorem shift_formula {j k : Nat} (h : Per j (2 ^ k)) :
    ∀ t, R (j + 1) (t + 2 ^ k) = xor (R (j + 1) t) (R (j + 1) (2 ^ k)) := by
  rcases j with _ | j
  · -- diagonal 1 alternates
    intro t
    rw [R_one_eq, R_one_eq, R_one_eq]
    rcases k with _ | k
    · rcases Nat.mod_two_eq_zero_or_one t with ht | ht
      · have : (t + 2 ^ 0) % 2 = 1 := by simp; omega
        simp [ht, this]
      · have : (t + 2 ^ 0) % 2 = 0 := by simp; omega
        simp [ht, this]
    · have e1 : (t + 2 ^ (k + 1)) % 2 = t % 2 := by rw [Nat.pow_succ]; omega
      have e2 : 2 ^ (k + 1) % 2 = 0 := by rw [Nat.pow_succ]; omega
      rw [e1, e2]; cases (t % 2 == 1) <;> rfl
  · have sh := accum_shift (x := R (j + 2)) (g := fun t => R (j + 1) t || R j t) (L := 2 ^ k)
      (fun t => R_step j t) (fun t => input_per h t)
    rw [R_init (show 1 ≤ j + 2 by omega)] at sh
    intro t; rw [sh t]; cases R (j + 2) (2 ^ k) <;> rfl

/-- **Doubling criterion**: given period `2^k` on diagonal `j`, diagonal `j + 1` keeps the period
`2^k` exactly when its cell at time `2^k` is white. -/
theorem per_succ_iff {j k : Nat} (h : Per j (2 ^ k)) :
    Per (j + 1) (2 ^ k) ↔ R (j + 1) (2 ^ k) = false := by
  constructor
  · intro hp
    have := hp 0
    rwa [Nat.zero_add, R_init (by omega)] at this
  · intro h0 t
    rw [shift_formula h t, h0]; cases R (j + 1) t <;> rfl

/-- When the period doubles, the diagonal is complemented by a shift of half its period. -/
theorem antiperiod {j k : Nat} (h : Per j (2 ^ k)) (hn : ¬ Per (j + 1) (2 ^ k)) :
    ∀ t, R (j + 1) (t + 2 ^ k) = !R (j + 1) t := by
  have h1 : R (j + 1) (2 ^ k) = true := by
    cases h' : R (j + 1) (2 ^ k)
    · exact absurd ((per_succ_iff h).2 h') hn
    · rfl
  intro t; rw [shift_formula h t, h1]; cases R (j + 1) t <;> rfl

/-- **Step**: the period at most doubles from one diagonal to the next (`e_{j+1} ≤ e_j + 1`). -/
theorem per_step {j k : Nat} (h : Per j (2 ^ k)) : Per (j + 1) (2 ^ (k + 1)) := by
  intro t
  rw [Nat.pow_succ, show 2 ^ k * 2 = 2 ^ k + 2 ^ k by omega, ← Nat.add_assoc,
    shift_formula h, shift_formula h]
  cases R (j + 1) t <;> cases R (j + 1) (2 ^ k) <;> rfl

/-! ### The rows at times `2^k u` -/

/-- **Zero gap.** Let `J` be a diagonal with period `2^k` whose successor does not have it. Then
at every time `2^k u` the diagonals `1, …, J` are white and diagonal `J + 1` is black exactly when
`u` is odd. -/
theorem zero_gap {J k : Nat} (hJ : Per J (2 ^ k)) (hJ1 : ¬ Per (J + 1) (2 ^ k)) (u : Nat) :
    (∀ i, 1 ≤ i → i ≤ J → R i (2 ^ k * u) = false) ∧
      R (J + 1) (2 ^ k * u) = (u % 2 == 1) := by
  refine ⟨fun i hi1 hiJ => ?_, ?_⟩
  · rw [(per_mono_le hiJ hJ).at_mul u, R_init hi1]
  · have anti := antiperiod hJ hJ1
    induction u with
    | zero => rw [Nat.mul_zero, R_init (by omega)]; rfl
    | succ u ih =>
      rw [Nat.mul_succ, anti, ih]
      rcases Nat.mod_two_eq_zero_or_one u with h | h
      · have h' : (u + 1) % 2 = 1 := by omega
        simp [h, h']
      · have h' : (u + 1) % 2 = 0 := by omega
        simp [h, h']

/-- The same in terms of cells: row `N = 2^k u` (`u` odd) reads `1 0^J 1` leftwards from its
right edge. -/
theorem zero_gap_cell {J k : Nat} (hJ : Per J (2 ^ k)) (hJ1 : ¬ Per (J + 1) (2 ^ k)) (u : Nat)
    (hu : u % 2 = 1) :
    (∀ i, 1 ≤ i → i ≤ J → cell (2 ^ k * u) ((2 ^ k * u : Nat) - (i : Int)) = false) ∧
      cell (2 ^ k * u) ((2 ^ k * u : Nat) - ((J + 1 : Nat) : Int)) = true := by
  obtain ⟨h1, h2⟩ := zero_gap hJ hJ1 u
  refine ⟨fun i hi1 hiJ => h1 i hi1 hiJ, ?_⟩
  have := h2
  rw [hu] at this
  exact this

/-- **The last cell of every period is black**: if diagonal `j` has period `2^k`, then
`R j (2^k - 1)` is black. So row `2^k - 1` ends in `J + 1` black cells. -/
theorem last_one : ∀ j k, Per j (2 ^ k) → R j (2 ^ k - 1) = true
  | 0, _, _ => R_zero _
  | 1, k, h => by
    rcases k with _ | k
    · exact absurd h (not_per_one (by omega))
    · rw [R_one_eq]
      have : (2 ^ (k + 1) - 1) % 2 = 1 := by
        have := Nat.two_pow_pos k; rw [Nat.pow_succ]; omega
      rw [this]; rfl
  | j + 2, k, h => by
    have hp := Nat.two_pow_pos k
    have hj1 := last_one (j + 1) k (per_mono h)
    have s := R_step j (2 ^ k - 1)
    rw [show 2 ^ k - 1 + 1 = 0 + 2 ^ k by omega, h 0, R_init (by omega), hj1] at s
    revert s; cases R (j + 2) (2 ^ k - 1) <;> simp

/-! ### Restarts at the right edge -/

/-- **Restart.** If diagonal `j` has period `2^k`, it reads the same at times `2^k u + s` and `s`. -/
theorem restart {j k : Nat} (h : Per j (2 ^ k)) (u s : Nat) : R j (2 ^ k * u + s) = R j s := by
  have := h.mul u s
  rwa [show s + u * 2 ^ k = 2 ^ k * u + s by rw [Nat.mul_comm]; omega] at this

/-- **The center column restarts at the right edge**: if diagonal `s` has period `2^k`, the cell
`s` steps below the right-edge cell `(2^k u, 2^k u)` equals `c(s)`. So column `2^k u` repeats
`c(0), …, c(J)` where `J` is the last diagonal of period `2^k`. -/
theorem center_restart {s k : Nat} (h : Per s (2 ^ k)) (u : Nat) :
    cell (2 ^ k * u + s) ((2 ^ k * u : Nat) : Int) = cell s 0 := by
  have := restart h u s
  unfold R at this
  rw [cell_congr (show ((2 ^ k * u + s : Nat) : Int) - (s : Int) = ((2 ^ k * u : Nat) : Int)
      by omega), cell_congr (show ((s : Nat) : Int) - (s : Int) = 0 by omega)] at this
  exact this

/-- **Columns are 2-adically continuous**: if diagonal `s` has period `2^k`, columns `p` and
`p + 2^k u` agree `s` steps after the right edge reaches them. -/
theorem column_continuity {s k : Nat} (h : Per s (2 ^ k)) (p u : Nat) :
    cell (p + 2 ^ k * u + s) ((p + 2 ^ k * u : Nat) : Int) = cell (p + s) (p : Int) := by
  have := h.mul u (p + s)
  unfold R at this
  rw [show p + s + u * 2 ^ k = p + 2 ^ k * u + s by rw [Nat.mul_comm]; omega,
    cell_congr (show ((p + 2 ^ k * u + s : Nat) : Int) - (s : Int) = ((p + 2 ^ k * u : Nat) : Int)
      by omega), cell_congr (show ((p + s : Nat) : Int) - (s : Int) = (p : Int) by omega)] at this
  exact this

/-- **A black center cell lies in the first period of its diagonal**: if `c(t)` is black and
diagonal `t` has period `2^k`, then `t < 2^k`. (If `2^k ≤ t`, then `t mod 2^k < t/2`, so by
periodicity `c(t)` equals a cell outside the light cone.) -/
theorem center_black_lt {t k : Nat} (hc : cell t 0 = true) (h : Per t (2 ^ k)) : t < 2 ^ k := by
  have hp := Nat.two_pow_pos k
  apply Nat.lt_of_not_le
  intro hle
  have e := h.mul (t / 2 ^ k) (t % 2 ^ k)
  rw [show t % 2 ^ k + t / 2 ^ k * 2 ^ k = t by
    have := Nat.div_add_mod t (2 ^ k); rw [Nat.mul_comm] at this; omega] at e
  have hmod : t % 2 ^ k < 2 ^ k := Nat.mod_lt _ hp
  have hmod2 : t % 2 ^ k + 2 ^ k ≤ t := by
    have h1 := Nat.div_add_mod t (2 ^ k)
    have h2 : 1 ≤ t / 2 ^ k := (Nat.le_div_iff_mul_le hp).2 (by omega)
    have h3 : 2 ^ k ≤ 2 ^ k * (t / 2 ^ k) := Nat.le_mul_of_pos_right _ (by omega)
    omega
  rw [R_lt (show 2 * (t % 2 ^ k) < t by omega)] at e
  have : R t t = cell t 0 := by
    unfold R; exact cell_congr (by omega)
  rw [this, hc] at e
  exact absurd e (by decide)

/-! ### No three doublings in a row -/

/-- **No three doublings.** If the period doubles from `j` to `j + 1` and again from `j + 1` to
`j + 2`, it stays from `j + 2` to `j + 3`.

With `H = 2^E`: diagonal `j + 1` is complemented by a shift of `H`, diagonal `j + 2` by a shift of
`2H`. The parity that diagonal `j + 3` accumulates over `4H` steps is the number of white cells of
diagonal `j + 1` in `2H` steps, which is `H`, even. -/
theorem no_three {j E : Nat} (hj : 1 ≤ j) (h0 : Per j (2 ^ E)) (h1 : ¬ Per (j + 1) (2 ^ E))
    (h2 : ¬ Per (j + 2) (2 ^ (E + 1))) : Per (j + 3) (2 ^ (E + 2)) := by
  -- `E ≥ 1`, since diagonal `j ≥ 1` is not constant
  have hE : 1 ≤ E := by
    rcases Nat.eq_zero_or_pos E with rfl | h
    · exact absurd h0 (not_per_one hj)
    · exact h
  obtain ⟨E', rfl⟩ : ∃ E', E = E' + 1 := ⟨E - 1, by omega⟩
  obtain ⟨H, hH⟩ : ∃ H, 2 ^ (E' + 1) = H := ⟨_, rfl⟩
  have hH2 : 2 ^ (E' + 1 + 1) = 2 * H := by rw [Nat.pow_succ, hH]; omega
  have hH4 : 2 ^ (E' + 1 + 2) = 4 * H := by
    rw [show E' + 1 + 2 = (E' + 1) + 1 + 1 by omega, Nat.pow_succ, Nat.pow_succ, hH]; omega
  have hHeven : H % 2 = 0 := by rw [← hH, Nat.pow_succ]; omega
  -- antiperiods
  have a1 : ∀ t, R (j + 1) (t + H) = !R (j + 1) t := by
    have := antiperiod h0 h1; rwa [hH] at this
  have p1 : Per (j + 1) (2 ^ (E' + 1 + 1)) := per_step h0
  have a2 : ∀ t, R (j + 2) (t + 2 * H) = !R (j + 2) t := by
    have := antiperiod p1 h2; rwa [hH2] at this
  have p2 : Per (j + 2) (2 ^ (E' + 1 + 2)) := per_step p1
  -- it suffices that diagonal `j + 3` is white at time `4H`
  have key : R (j + 3) (4 * H) = false := by
    let x := R (j + 3)
    have hx : ∀ t, x (t + 1) = xor (x t) (R (j + 2) t || R (j + 1) t) := fun t => R_step (j + 1) t
    -- `u t = x (t + 2H) xor x t` accumulates `not (R (j+1) t)`
    let u := fun t => xor (x (t + 2 * H)) (x t)
    have hu : ∀ t, u (t + 1) = xor (u t) (!R (j + 1) t) := by
      intro t
      show xor (x (t + 1 + 2 * H)) (x (t + 1)) = xor (xor (x (t + 2 * H)) (x t)) (!R (j + 1) t)
      have p1' : R (j + 1) (t + 2 * H) = R (j + 1) t := by
        rw [show t + 2 * H = (t + H) + H by omega, a1, a1]; cases R (j + 1) t <;> rfl
      rw [show t + 1 + 2 * H = (t + 2 * H) + 1 by omega, hx, hx, a2, p1']
      cases x (t + 2 * H) <;> cases x t <;> cases R (j + 2) t <;> cases R (j + 1) t <;> rfl
    -- `v t = u (t + H) xor u t` flips every step
    let v := fun t => xor (u (t + H)) (u t)
    have hv : ∀ t, v (t + 1) = !v t := by
      intro t
      show xor (u (t + 1 + H)) (u (t + 1)) = !(xor (u (t + H)) (u t))
      rw [show t + 1 + H = (t + H) + 1 by omega, hu, hu, a1]
      cases u (t + H) <;> cases u t <;> cases R (j + 1) t <;> rfl
    have hvH : ∀ n, v (n + 2) = v n := fun n => by rw [hv, hv]; cases v n <;> rfl
    have hvper : ∀ n, v (2 * n) = v 0 := by
      intro n; induction n with
      | zero => rfl
      | succ n ih => rw [show 2 * (n + 1) = 2 * n + 2 by omega, hvH, ih]
    have hvH' : v H = v 0 := by
      obtain ⟨m, hm⟩ : ∃ m, H = 2 * m := ⟨H / 2, by omega⟩
      rw [hm]; exact hvper m
    -- assemble
    have ex0 : x 0 = false := R_init (by omega)
    have e1 : x (4 * H) = xor (x (2 * H)) (u (2 * H)) := by
      show x (4 * H) = xor (x (2 * H)) (xor (x (2 * H + 2 * H)) (x (2 * H)))
      rw [show 2 * H + 2 * H = 4 * H by omega]; cases x (4 * H) <;> cases x (2 * H) <;> rfl
    have e2 : x (2 * H) = u 0 := by
      show x (2 * H) = xor (x (0 + 2 * H)) (x 0)
      rw [Nat.zero_add, ex0]; cases x (2 * H) <;> rfl
    have e3 : u (2 * H) = xor (u H) (v H) := by
      show u (2 * H) = xor (u H) (xor (u (H + H)) (u H))
      rw [show H + H = 2 * H by omega]; cases u (2 * H) <;> cases u H <;> rfl
    have e4 : u H = xor (u 0) (v 0) := by
      show u H = xor (u 0) (xor (u (0 + H)) (u 0))
      rw [Nat.zero_add]; cases u H <;> cases u 0 <;> rfl
    show x (4 * H) = false
    rw [e1, e2, e3, e4, hvH']
    cases u 0 <;> cases v 0 <;> rfl
  have p3 := per_succ_iff p2
  rw [hH4] at p3 ⊢
  exact p3.2 key

/-! ### Bounds -/

/-- **Lower bound**: diagonal `j ≥ 1` does not repeat with period `2^k` when `2^(k+1) ≤ j`. So
`j < 2^(e_j + 1)`, and the periods are unbounded. -/
theorem not_per_small {j k : Nat} (hj : 1 ≤ j) (hk : 2 ^ (k + 1) ≤ j) : ¬ Per j (2 ^ k) := by
  intro h
  have hp := Nat.two_pow_pos k
  have h2 : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ]; omega
  have := h ((j + 1) / 2 - 2 ^ k)
  rw [show (j + 1) / 2 - 2 ^ k + 2 ^ k = (j + 1) / 2 by omega, R_half hj,
    R_lt (show 2 * ((j + 1) / 2 - 2 ^ k) < j by omega)] at this
  exact absurd this (by decide)

/-- Three diagonals on, the period grows by a factor at most `4`. -/
theorem per_three {j k : Nat} (hj : 1 ≤ j) (h : Per j (2 ^ k)) : Per (j + 3) (2 ^ (k + 2)) := by
  by_cases h1 : Per (j + 1) (2 ^ k)
  · exact per_step (per_step h1)
  · by_cases h2 : Per (j + 2) (2 ^ (k + 1))
    · exact per_step h2
    · exact no_three hj h h1 h2

/-- **Upper bound**: `e_j ≤ (2j + 1)/3` for `j ≥ 2`. -/
theorem per_upper : ∀ j, 2 ≤ j → Per j (2 ^ ((2 * j + 1) / 3))
  | 0, h => absurd h (by omega)
  | 1, h => absurd h (by omega)
  | 2, _ => by
    show Per 2 (2 ^ 1)
    intro t; rw [R_two_eq_one, R_two_eq_one]; exact per_one 0 t
  | 3, _ => by
    show Per (2 + 1) (2 ^ (1 + 1))
    apply per_step; intro t; rw [R_two_eq_one, R_two_eq_one]; exact per_one 0 t
  | 4, _ => by
    show Per (2 + 1 + 1) (2 ^ (1 + 1 + 1))
    apply per_step; apply per_step; intro t; rw [R_two_eq_one, R_two_eq_one]; exact per_one 0 t
  | j + 5, _ => by
    have ih := per_upper (j + 2) (by omega)
    have := per_three (show 1 ≤ j + 2 by omega) ih
    rw [show j + 2 + 3 = j + 5 by omega,
      show (2 * (j + 2) + 1) / 3 + 2 = (2 * (j + 5) + 1) / 3 by omega] at this
    exact this

/-! ### Periods read off the rows at powers of two -/

/-- **Gap characterization**: diagonal `n` repeats with period `2^k` exactly when row `2^k` has
`n` white cells immediately left of its right edge. So `e_n` is the least `k` such that row `2^k`
ends in `1` preceded by at least `n` white cells. -/
theorem per_iff_gap (k n : Nat) :
    Per n (2 ^ k) ↔ ∀ i, 1 ≤ i → i ≤ n → R i (2 ^ k) = false := by
  constructor
  · intro h i hi1 hin
    have := (per_mono_le hin h).at_mul 1
    rwa [Nat.mul_one, R_init hi1] at this
  · induction n with
    | zero => intro _; exact per_zero _
    | succ n ih =>
      intro h
      have hn := ih (fun i h1 h2 => h i h1 (by omega))
      exact (per_succ_iff hn).2 (h (n + 1) (by omega) (Nat.le_refl _))

/-- Cells of the packed simulation `Rule30Window.row`. -/
theorem R_eq_row (j t K : Nat) (ht : t ≤ K) (hj : j ≤ t + K) :
    R j t = (Rule30Window.row K t).testBit (t + K - j) := by
  rw [Rule30Window.row_testBit K t ht]
  show cell t ((t : Int) - j) = cell t (((t + K - j : Nat) : Int) - K)
  exact cell_congr (by omega)

/-- Row `64` ends in `1` preceded by `14` white cells, so diagonal `14` has period `2^6 = 64`.
In particular `e_14 ≤ 6 < 7 = ⌊14/2⌋`: the guess `e_j ≥ ⌊j/2⌋` is false. -/
theorem per_14 : Per 14 (2 ^ 6) := by
  rw [per_iff_gap]
  intro i hi1 hi
  rw [R_eq_row i (2 ^ 6) 64 (by decide) (by omega)]
  have hall : (List.range 14).all (fun i => !(Rule30Window.row 64 64).testBit (128 - (i + 1)))
      = true := by decide +kernel
  rw [List.all_eq_true] at hall
  have := hall (i - 1) (List.mem_range.2 (by omega))
  rw [show 128 - (i - 1 + 1) = 2 ^ 6 + 64 - i by omega] at this
  revert this; cases (Rule30Window.row 64 64).testBit (2 ^ 6 + 64 - i) <;> simp

/-- Row `256` ends in `1` preceded by `23` white cells: `e_23 ≤ 8 < 11 = ⌊23/2⌋`. -/
theorem per_23 : Per 23 (2 ^ 8) := by
  rw [per_iff_gap]
  intro i hi1 hi
  rw [R_eq_row i (2 ^ 8) 256 (by decide) (by omega)]
  have hall : (List.range 23).all (fun i => !(Rule30Window.row 256 256).testBit (512 - (i + 1)))
      = true := by decide +kernel
  rw [List.all_eq_true] at hall
  have := hall (i - 1) (List.mem_range.2 (by omega))
  rw [show 512 - (i - 1 + 1) = 2 ^ 8 + 256 - i by omega] at this
  revert this; cases (Rule30Window.row 256 256).testBit (2 ^ 8 + 256 - i) <;> simp

/-- `e_j ≥ ⌊j/2⌋` fails: diagonal `14` repeats with a period below `2^7`. -/
theorem not_half_lower : ¬ ∀ j k, Per j (2 ^ k) → j / 2 ≤ k := by
  intro h
  have := h 14 6 per_14
  omega

end Rule30RightPeriods
end Ruliology.CellularAutomata

/-! ## Independent check of the claim `restart_continuity_black_centers` (verifier scratch) -/

namespace Ruliology.CellularAutomata
namespace ClaimCheck
open Rule30Jen Rule30Diagonals Rule30RightPeriods

/-- The last diagonal (at or after `j`) carrying period `H` exists once some later one lacks it. -/
theorem exists_last {H : Nat} : ∀ n j, Per j H → ¬ Per (j + n) H →
    ∃ J, j ≤ J ∧ Per J H ∧ ¬ Per (J + 1) H
  | 0, j, h, hn => absurd h (by simpa using hn)
  | n + 1, j, h, hn => by
    by_cases h1 : Per (j + 1) H
    · obtain ⟨J, hJ, h2, h3⟩ :=
        exists_last n (j + 1) h1 (by rwa [show j + 1 + n = j + (n + 1) by omega])
      exact ⟨J, by omega, h2, h3⟩
    · exact ⟨j, Nat.le_refl _, h, h1⟩

/-- `J` with `Per J`, `¬ Per (J+1)` is the maximum of `{j | Per j (2^k)}` (monotonicity). -/
theorem last_is_max {J k : Nat} (hJ1 : ¬ Per (J + 1) (2 ^ k)) :
    ∀ j, Per j (2 ^ k) → j ≤ J := by
  intro j hj
  apply Nat.le_of_not_lt
  intro hlt
  exact hJ1 (per_mono_le (show J + 1 ≤ j by omega) hj)

/-- `J_E` is finite: some `J ≥ 0` has period `2^E` and its successor does not. -/
theorem J_exists (E : Nat) : ∃ J, Per J (2 ^ E) ∧ ¬ Per (J + 1) (2 ^ E) := by
  have hbig : ¬ Per (0 + 2 ^ (E + 1)) (2 ^ E) :=
    not_per_small (by have := Nat.two_pow_pos (E + 1); omega) (by omega)
  obtain ⟨J, _, h2, h3⟩ := exists_last (2 ^ (E + 1)) 0 (per_zero _) hbig
  exact ⟨J, h2, h3⟩

/-- (a) general form: if `2^k ∣ N` and `R_J` has period `2^k`, then
`cell (N+s) (N+q) = cell s q` whenever `0 ≤ s - q ≤ J`. -/
theorem restart_general {N k J s : Nat} {q : Int} (hN : 2 ^ k ∣ N) (hJ : Per J (2 ^ k))
    (hq0 : q ≤ (s : Int)) (hqJ : (s : Int) - q ≤ (J : Int)) :
    cell (N + s) ((N : Int) + q) = cell s q := by
  obtain ⟨m, hm⟩ := hN
  have hj : (((s : Int) - q).toNat : Int) = (s : Int) - q := Int.toNat_of_nonneg (by omega)
  have hjJ : ((s : Int) - q).toNat ≤ J := by omega
  have hp : Per ((s : Int) - q).toNat (2 ^ k) := per_mono_le hjJ hJ
  have := hp.mul m s
  unfold R at this
  have e1 : s + m * 2 ^ k = N + s := by rw [hm, Nat.mul_comm]; omega
  rw [e1] at this
  rw [cell_congr (show ((N + s : Nat) : Int) - ((((s : Int) - q).toNat : Nat) : Int)
        = (N : Int) + q by omega),
      cell_congr (show ((s : Nat) : Int) - ((((s : Int) - q).toNat : Nat) : Int) = q by omega)]
    at this
  exact this

/-- (a) column `2^k u` repeats `c(0..J)`. -/
theorem column_repeats {J k s : Nat} (hJ : Per J (2 ^ k)) (hs : s ≤ J) (u : Nat) :
    cell (2 ^ k * u + s) ((2 ^ k * u : Nat) : Int) = cell s 0 :=
  center_restart (per_mono_le hs hJ) u

/-- (a) the flip: for `u` odd, `cell (2^k u + J + 1) (2^k u) = ¬ c(J+1)`. -/
theorem column_flip {J k u : Nat} (hJ : Per J (2 ^ k)) (hJ1 : ¬ Per (J + 1) (2 ^ k))
    (hu : u % 2 = 1) :
    cell (2 ^ k * u + (J + 1)) ((2 ^ k * u : Nat) : Int) = !cell (J + 1) 0 := by
  have anti := antiperiod hJ hJ1
  have key : ∀ u, R (J + 1) (2 ^ k * u + (J + 1)) = xor (R (J + 1) (J + 1)) (u % 2 == 1) := by
    intro u
    induction u with
    | zero => simp
    | succ u ih =>
      rw [show 2 ^ k * (u + 1) + (J + 1) = (2 ^ k * u + (J + 1)) + 2 ^ k by
        rw [Nat.mul_succ]; omega, anti, ih]
      rcases Nat.mod_two_eq_zero_or_one u with h | h
      · have h' : (u + 1) % 2 = 1 := by omega
        rw [h, h']; cases R (J + 1) (J + 1) <;> rfl
      · have h' : (u + 1) % 2 = 0 := by omega
        rw [h, h']; cases R (J + 1) (J + 1) <;> rfl
  have := key u
  rw [hu] at this
  unfold R at this
  rw [cell_congr (show ((2 ^ k * u + (J + 1) : Nat) : Int) - ((J + 1 : Nat) : Int)
        = ((2 ^ k * u : Nat) : Int) by omega),
      cell_congr (show ((J + 1 : Nat) : Int) - ((J + 1 : Nat) : Int) = 0 by omega)] at this
  rw [this]; cases cell (J + 1) 0 <;> rfl

/-- (b) a black center cell lies in the first period of its diagonal (restated). -/
theorem black_center {t k : Nat} (hc : cell t 0 = true) (h : Per t (2 ^ k)) : t < 2 ^ k :=
  center_black_lt hc h

/-- (c) If `R_t` has period `2^E ≤ t` (`t ≥ 1`), then with `J` the last diagonal of period
`2^E` (which exists and is the maximum), `t ≤ J` and `c = 0` on `[2^E, J]`. -/
theorem zero_run {t E : Nat} (ht : 1 ≤ t) (hper : Per t (2 ^ E)) (hle : 2 ^ E ≤ t) :
    ∃ J, t ≤ J ∧ Per J (2 ^ E) ∧ ¬ Per (J + 1) (2 ^ E) ∧ (∀ j, Per j (2 ^ E) → j ≤ J) ∧
      ∀ t', 2 ^ E ≤ t' → t' ≤ J → cell t' 0 = false := by
  have hpos := Nat.two_pow_pos (E + 1)
  have hbig : ¬ Per (t + 2 ^ (E + 1)) (2 ^ E) := not_per_small (by omega) (by omega)
  obtain ⟨J, htJ, hJ, hJ1⟩ := exists_last (2 ^ (E + 1)) t hper hbig
  refine ⟨J, htJ, hJ, hJ1, last_is_max hJ1, fun t' h1 h2 => ?_⟩
  cases hc : cell t' 0
  · rfl
  · have := center_black_lt hc (per_mono_le h2 hJ)
    omega

end ClaimCheck
end Ruliology.CellularAutomata

open Ruliology.CellularAutomata.ClaimCheck in
#print axioms restart_general
open Ruliology.CellularAutomata.ClaimCheck in
#print axioms column_flip
open Ruliology.CellularAutomata.ClaimCheck in
#print axioms zero_run
open Ruliology.CellularAutomata.ClaimCheck in
#print axioms J_exists
