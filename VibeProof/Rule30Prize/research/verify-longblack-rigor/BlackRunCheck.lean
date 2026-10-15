import Ruliology.CellularAutomata.Rule30Prize

/-!
# Long black runs in a column force its right neighbours

**Black-run lemma** (`black_run`): if the center column of rule 30 is black at nine consecutive times
`t, …, t+8`, then at time `t+9` column `1` is white and column `2` is black.

The right half of rule 30 is driven by column `0`: cells `1..11` at time `t` and the colors of column `0`
determine cells `1, 2` nine steps later.  The statement is checked for all `2^11` rows by `decide`
(`black9_check`) and transported to `cell` by `iterR_rowR`.

**Corollary** (`not_eventually_periodic_of_long_black_runs`): the center column is not eventually
periodic with a repeating block in which every maximal run of black cells has length at least nine.
For a white time `z` of the center column after such a run, column 1 is white at `z` and black at
every later time of the same white run (column 1 is monotone while the center is white and column 2
is black at `z`).  So column 1 restricted to the white times of the center column is eventually
periodic, which `masked_jen` rules out.
-/

namespace R30NewIdeas
open Ruliology.CellularAutomata.Rule30Jen

/-- One rule-30 pass over a list: `[a, b, c, …] ↦ [rule a b c, …]` (length shrinks by two). -/
def lin3 : List Bool → List Bool
  | a :: b :: c :: rest => xor a (b || c) :: lin3 (b :: c :: rest)
  | _ => []

/-- `k` steps of the right strip with column 0 held at `c0`. -/
def iterR (c0 : Bool) : Nat → List Bool → List Bool
  | 0, row => row
  | k + 1, row => iterR c0 k (lin3 (c0 :: row))

/-- All `2^11` rows: nine black center steps make column 1 white and column 2 black. -/
theorem black9_check : ∀ b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 : Bool,
    iterR true 9 [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11] = [false, true] := by
  decide

/-- The list `[f 0, f 1, …, f (n-1)]`. -/
def seg (f : Nat → Bool) : Nat → List Bool
  | 0 => []
  | n + 1 => f 0 :: seg (fun i => f (i + 1)) n

theorem lin3_seg : ∀ (m : Nat) (f : Nat → Bool),
    lin3 (seg f (m + 2)) = seg (fun i => xor (f i) (f (i + 1) || f (i + 2))) m
  | 0, f => rfl
  | m + 1, f => by
    show xor (f 0) (f 1 || f 2) :: lin3 (seg (fun i => f (i + 1)) (m + 2)) = _
    rw [lin3_seg m (fun i => f (i + 1))]
    rfl

/-- Columns `1..m` at time `t`. -/
def rowR (t m : Nat) : List Bool := seg (fun i => cell t ((i : Int) + 1)) m

theorem cons_rowR (t m : Nat) :
    cell t 0 :: rowR t m = seg (fun i => cell t (i : Int)) (m + 1) := by
  show cell t 0 :: seg (fun i => cell t ((i : Int) + 1)) m = cell t ((0 : Nat) : Int) :: seg _ m
  congr 2

theorem lin3_rowR (t m : Nat) (h : cell t 0 = true) : lin3 (true :: rowR t (m + 1)) = rowR (t + 1) m := by
  rw [← h, cons_rowR, lin3_seg]
  unfold rowR
  congr 1
  funext i
  show xor (cell t (i : Int)) (cell t ((i + 1 : Nat) : Int) || cell t ((i + 2 : Nat) : Int)) =
    rule (cell t ((i : Int) + 1 - 1)) (cell t ((i : Int) + 1)) (cell t ((i : Int) + 1 + 1))
  rw [show ((i : Int) + 1 - 1) = (i : Int) by omega, show ((i + 1 : Nat) : Int) = (i : Int) + 1 by omega,
    show ((i + 2 : Nat) : Int) = (i : Int) + 1 + 1 by omega]
  rfl

theorem iterR_rowR : ∀ (k n t : Nat), (∀ j, j < k → cell (t + j) 0 = true) →
    iterR true k (rowR t (n + k)) = rowR (t + k) n
  | 0, n, t, _ => rfl
  | k + 1, n, t, h => by
    show iterR true k (lin3 (true :: rowR t (n + k + 1))) = _
    rw [lin3_rowR t (n + k) (by simpa using h 0 (by omega))]
    rw [iterR_rowR k n (t + 1) (fun j hj => by rw [show t + 1 + j = t + (j + 1) by omega]; exact h (j + 1) (by omega))]
    rw [show t + 1 + k = t + (k + 1) by omega]

/-- **Black-run lemma.** Nine consecutive black center cells force column 1 white and column 2 black. -/
theorem black_run (t : Nat) (h : ∀ j, j < 9 → cell (t + j) 0 = true) :
    cell (t + 9) 1 = false ∧ cell (t + 9) 2 = true := by
  have e := iterR_rowR 9 2 t h
  have hrow : rowR t (2 + 9) = [cell t 1, cell t 2, cell t 3, cell t 4, cell t 5, cell t 6, cell t 7,
      cell t 8, cell t 9, cell t 10, cell t 11] := rfl
  rw [hrow, black9_check] at e
  have hrow2 : rowR (t + 9) 2 = [cell (t + 9) 1, cell (t + 9) 2] := rfl
  rw [hrow2] at e
  simp only [List.cons.injEq] at e
  exact ⟨e.1.symm, e.2.1.symm⟩

/-- **Masked Jen.** Column `i` and column `i+1` restricted to the zeros of column `i` are never jointly
eventually periodic. -/
theorem masked_jen (i : Int) {T Q : Nat} (hQ : 0 < Q)
    (h0 : ∀ t, T ≤ t → cell (t + Q) i = cell t i)
    (h1 : ∀ t, T ≤ t → cell t i = false → cell (t + Q) (i + 1) = cell t (i + 1)) : False := by
  have hm : ∀ t, T ≤ t → cell (t + Q) (i - 1) = cell t (i - 1) := by
    intro t ht
    rw [cell_left (t + Q) i, cell_left t i, show t + Q + 1 = (t + 1) + Q by omega,
      h0 (t + 1) (by omega), h0 t ht]
    cases hc : cell t i with
    | false => rw [h1 t ht hc]
    | true => rfl
  have e : i - 1 + 1 = i := by omega
  refine not_adjacent (i - 1) ⟨T, Q, hQ, hm⟩ ?_
  rw [e]
  exact ⟨T, Q, hQ, h0⟩


/-- Inside a white run of the center column that follows nine black cells, column 1 is white at the
first white time and black afterwards. -/
theorem col1_after_black_run (z : Nat) (h9 : ∀ j, j < 9 → cell (z - 9 + j) 0 = true) (hz : 9 ≤ z) :
    ∀ k, (∀ i, i ≤ k → cell (z + i) 0 = false) → cell (z + k) 1 = decide (0 < k) := by
  have hb := black_run (z - 9) h9
  rw [show z - 9 + 9 = z by omega] at hb
  intro k
  induction k with
  | zero => intro _; simpa using hb.1
  | succ k ih =>
    intro hw
    have hwk : cell (z + k) 0 = false := hw k (by omega)
    show rule (cell (z + k) (1 - 1)) (cell (z + k) 1) (cell (z + k) (1 + 1)) = decide (0 < k + 1)
    rw [show (1 : Int) - 1 = 0 by rfl, hwk]
    cases k with
    | zero => simp [rule, hb.2]
    | succ k =>
      rw [ih (fun i hi => hw i (by omega))]
      simp [rule]

/-- **Corollary of the black-run lemma.** If the center column is eventually periodic, it is not the
case that (from some time on) every white cell lies in a white run preceded by at least nine black
cells. -/
theorem not_eventually_periodic_of_long_black_runs (T P T' : Nat) (hP : 0 < P)
    (hper : ∀ t, T ≤ t → cell (t + P) 0 = cell t 0)
    (hrun : ∀ t, T' ≤ t → cell t 0 = false → ∃ k, k + 10 ≤ t ∧ (∀ i, i ≤ k → cell (t - i) 0 = false) ∧
      (∀ j, j < 9 → cell (t - k - 9 + j) 0 = true)) : False := by
  -- column 1 at white times is the negation of the previous center cell
  have key : ∀ t, T' ≤ t → cell t 0 = false → cell t 1 = !cell (t - 1) 0 := by
    intro t ht hw
    obtain ⟨k, hk, hwhite, hblack⟩ := hrun t ht hw
    have := col1_after_black_run (t - k) (fun j hj => hblack j hj) (by omega) k
      (fun i hi => by rw [show t - k + i = t - (k - i) by omega]; exact hwhite (k - i) (by omega))
    rw [show t - k + k = t by omega] at this
    rw [this]
    cases k with
    | zero =>
      have hb : cell (t - 1) 0 = true := by
        have := hblack 8 (by omega); rwa [show t - 0 - 9 + 8 = t - 1 by omega] at this
      simp [hb]
    | succ k =>
      have hw1 : cell (t - 1) 0 = false := hwhite 1 (by omega)
      simp [hw1]
  refine masked_jen 0 hP (T := max T T' + 1) (fun t ht => hper t (by omega)) ?_
  intro t ht hw
  have hw' : cell (t + P) 0 = false := by rw [hper t (by omega)]; exact hw
  rw [show (0 : Int) + 1 = 1 by rfl]
  rw [key t (by omega) hw, key (t + P) (by omega) hw', show t + P - 1 = (t - 1) + P by omega,
    hper (t - 1) (by omega)]

/-- Instance: for every `k ≥ 9`, the center column is not eventually `(0 1^k)`-periodic, i.e. there is
no `T` with `cell t 0 = decide ((t - T) % (k+1) ≠ 0)` for all `t ≥ T`. -/
theorem not_eventually_zero_ones (k : Nat) (hk : 9 ≤ k) (T : Nat)
    (h : ∀ t, T ≤ t → cell t 0 = decide ((t - T) % (k + 1) ≠ 0)) : False := by
  refine not_eventually_periodic_of_long_black_runs T (k + 1) (T + k + 11) (by omega) ?_ ?_
  · intro t ht
    rw [h (t + (k + 1)) (by omega), h t ht, show t + (k + 1) - T = (t - T) + (k + 1) by omega,
      Nat.add_mod_right]
  · intro t ht hw
    rw [h t (by omega)] at hw
    have hz : (t - T) % (k + 1) = 0 := by simpa using hw
    refine ⟨0, by omega, fun i hi => ?_, fun j hj => ?_⟩
    · rw [show i = 0 by omega, Nat.sub_zero, h t (by omega)]; simpa using hz
    · rw [h _ (by omega)]
      simp only [decide_eq_true_eq]
      intro hm
      -- (t - T) ≡ 0 and t - 9 + j - T = (t - T) - (9 - j) with 1 ≤ 9 - j ≤ 9 < k + 1
      have e : t - 0 - 9 + j - T = (t - T) - (9 - j) := by omega
      rw [e] at hm
      have h1 : (t - T) = (k + 1) * ((t - T) / (k + 1)) := by
        have := Nat.div_add_mod (t - T) (k + 1); omega
      have hq : 1 ≤ (t - T) / (k + 1) := by
        rcases Nat.eq_zero_or_pos ((t - T) / (k + 1)) with h0 | h0
        · rw [h0] at h1; omega
        · exact h0
      have : (t - T) - (9 - j) = (k + 1) * ((t - T) / (k + 1) - 1) + (k + 1 - (9 - j)) := by
        rw [Nat.mul_sub, Nat.mul_one]; omega
      rw [this, Nat.mul_add_mod] at hm
      rw [Nat.mod_eq_of_lt (by omega)] at hm
      omega

end R30NewIdeas

#print axioms R30NewIdeas.black_run
#print axioms R30NewIdeas.not_eventually_periodic_of_long_black_runs
#print axioms R30NewIdeas.not_eventually_zero_ones

set_option pp.fullNames true in
#check @R30NewIdeas.not_eventually_periodic_of_long_black_runs
set_option pp.fullNames true in
#check @R30NewIdeas.not_eventually_zero_ones
set_option pp.fullNames true in
#check @R30NewIdeas.black_run
set_option pp.fullNames true in
#print R30NewIdeas.rowR
#print axioms Ruliology.CellularAutomata.Rule30Jen.not_adjacent
#print axioms R30NewIdeas.masked_jen
-- sanity: the hypothesis form applied to the real Problem1 statement
example (H : ∃ T', ∀ t, T' ≤ t → Ruliology.CellularAutomata.Rule30Jen.cell t 0 = false →
    ∃ k, k + 10 ≤ t ∧ (∀ i, i ≤ k → Ruliology.CellularAutomata.Rule30Jen.cell (t - i) 0 = false) ∧
      (∀ j, j < 9 → Ruliology.CellularAutomata.Rule30Jen.cell (t - k - 9 + j) 0 = true)) :
    ¬ Ruliology.CellularAutomata.Rule30Jen.EventuallyPeriodic Ruliology.CellularAutomata.Rule30Prize.center := by
  rintro ⟨T, P, hP, hper⟩
  obtain ⟨T', hT'⟩ := H
  exact R30NewIdeas.not_eventually_periodic_of_long_black_runs T P T' hP hper hT'
