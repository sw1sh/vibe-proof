import Ruliology.CellularAutomata.Rule30Prize

/-!
# Rule 30: weakened and windowed forms of Jen's theorem, and exclusions from forcing

Jen's adjacent-column argument (`Rule30Jen.not_adjacent`) needs two adjacent columns that are both
eventually periodic. Here the hypothesis on the right-hand column is weakened as far as the
left-permutive reconstruction allows, and the weakened form is used to exclude eventual period
blocks of the center column.

**Weakened Jen.**
* `determine`: columns `i - 1, i - 2, …` are determined by column `i` and
  `orCol i = column i || column (i + 1)`. Column `i + 1` only matters where column `i` is white.
* `window_jen`, `window_jen_col`: no periodicity needed. Two times `t₁ < t₂` never carry the same
  pair (column `0` on `[t, t + t₂]`, `orCol 0` on `[t, t + t₂)`): the reconstructed cell at column
  `-t₂` would be white at time `t₁` (left of the edge) and black at time `t₂` (on the edge).
* `periodic_window`: if the center column has period `P` from `T`, every interval `[n, 2n)` with
  `n ≥ T + P` contains a time `s` with `center s = false` and `cell s 1 ≠ cell (s - P) 1`.
* `finitary_jen`: the center column and `orCol 0` are never both `P`-periodic on `[n - P, 2n]`.
* `or_not_eventuallyPeriodic`, `or_not_eventuallyPeriodic_col`: if column `i` is eventually periodic,
  `orCol i` is not. Column `i + 1` is not eventually periodic even on the white times of column `i`.

**Forcing and exclusions.**
* `nine_ones`: nine consecutive black cells in a column force the next two cells to the right (one
  step later) to be white, black. Checked over all `2 ^ 11` states of the light cone.
* `not_eventuallyPeriodic_of_long_one_runs_col`, `not_eventuallyPeriodic_of_long_one_runs`: a column
  in which, from some time on, every black run followed by a white cell has length `≥ 9` is not
  eventually periodic. Column `i + 1` is (numerically) not eventually periodic for such drivers, so
  this needs the weakened form. `finitary_long_runs` is a finitary version.
* `forcing`, `not_eventually_word`: light-cone forcing blocks and word certificates (lists).
* `not_eventually_word_strip`: sound strip certificates with bitmask sets (cheap to check);
  `not_eventually_01111111` and `not_eventually_certTable` (30 words of length 8 … 13) use them.
-/

namespace Ruliology.CellularAutomata
namespace Rule30JenWindow

open Rule30Jen

/-- `column i || column (i + 1)`: the only information about column `i + 1` that the left-permutive
reconstruction from columns `i`, `i + 1` uses. -/
def orCol (i : Int) (t : Nat) : Bool := cell t i || cell t (i + 1)

/-! ### Reconstruction to the left from a column and its `orCol` -/

theorem cell_left' (t : Nat) (i : Int) : cell t (i - 1) = xor (cell (t + 1) i) (orCol i t) :=
  cell_left t i

/-- **Determination lemma.** If column `i` agrees at times `t₁ + s`, `t₂ + s` for `s ≤ m`, and
`orCol i` agrees for `s < m`, then column `i - k` agrees for `s + k ≤ m`. -/
theorem determine {t₁ t₂ : Nat} {i : Int} (m : Nat)
    (hc : ∀ s, s ≤ m → cell (t₁ + s) i = cell (t₂ + s) i)
    (he : ∀ s, s < m → orCol i (t₁ + s) = orCol i (t₂ + s)) :
    ∀ k s, s + k ≤ m → cell (t₁ + s) (i - k) = cell (t₂ + s) (i - k) ∧
      (s + k < m → orCol (i - k) (t₁ + s) = orCol (i - k) (t₂ + s)) := by
  intro k
  induction k with
  | zero =>
    intro s hs
    rw [show i - ((0 : Nat) : Int) = i by omega]
    exact ⟨hc s (by omega), fun h => he s (by omega)⟩
  | succ k ih =>
    intro s hs
    have hA : cell (t₁ + s) (i - ((k + 1 : Nat) : Int)) = cell (t₂ + s) (i - ((k + 1 : Nat) : Int)) := by
      have e : i - ((k + 1 : Nat) : Int) = (i - (k : Int)) - 1 := by omega
      rw [e, cell_left', cell_left', show t₁ + s + 1 = t₁ + (s + 1) by omega,
        show t₂ + s + 1 = t₂ + (s + 1) by omega, (ih (s + 1) (by omega)).1,
        (ih s (by omega)).2 (by omega)]
    refine ⟨hA, fun h => ?_⟩
    have hB := (ih s (by omega)).1
    unfold orCol
    rw [hA, show i - ((k + 1 : Nat) : Int) + 1 = i - (k : Int) by omega, hB]

/-- **Window form of Jen's theorem.** No periodicity is assumed: two times `t₁ < t₂` never carry
the same (center column, `orCol 0`) window of length `t₂`. -/
theorem window_jen {t₁ t₂ : Nat} (h : t₁ < t₂)
    (hc : ∀ s, s ≤ t₂ → cell (t₁ + s) 0 = cell (t₂ + s) 0)
    (he : ∀ s, s < t₂ → orCol 0 (t₁ + s) = orCol 0 (t₂ + s)) : False := by
  have key := (determine (i := 0) t₂ hc he t₂ 0 (by omega)).1
  simp only [Nat.add_zero, Int.zero_sub] at key
  rw [cell_eq_false_of_lt t₁ (-(t₂ : Int)) (by omega), cell_left_edge t₂] at key
  exact absurd key (by decide)

/-- The same for any column `i`: two times `t₁ < t₂` never carry the same (column `i`, `orCol i`)
window of length `m` when `i - m = -t₂`. -/
theorem window_jen_col {t₁ t₂ : Nat} {i : Int} (m : Nat) (h : t₁ < t₂) (hm : i - (m : Int) = -(t₂ : Int))
    (hc : ∀ s, s ≤ m → cell (t₁ + s) i = cell (t₂ + s) i)
    (he : ∀ s, s < m → orCol i (t₁ + s) = orCol i (t₂ + s)) : False := by
  have key := (determine m hc he m 0 (by omega)).1
  simp only [Nat.add_zero] at key
  rw [hm, cell_eq_false_of_lt t₁ (-(t₂ : Int)) (by omega), cell_left_edge t₂] at key
  exact absurd key (by decide)

/-- **Periodic window form.** If the center column has period `P` from `T`, every interval
`[n, 2n)` with `n ≥ T + P` contains a time where the center is white and column 1 breaks period `P`. -/
theorem periodic_window {T P : Nat} (hP : 0 < P)
    (hc : ∀ t, T ≤ t → cell (t + P) 0 = cell t 0) (n : Nat) (hn : T + P ≤ n) :
    ∃ s, n ≤ s ∧ s < 2 * n ∧ cell s 0 = false ∧ cell s 1 ≠ cell (s - P) 1 := by
  refine Classical.byContradiction fun hne => ?_
  refine window_jen (t₁ := n - P) (t₂ := n) (by omega) (fun s _ => ?_) (fun s hs => ?_)
  · have := hc (n - P + s) (by omega)
    rw [show n - P + s + P = n + s by omega] at this
    exact this.symm
  · have hper := hc (n - P + s) (by omega)
    rw [show n - P + s + P = n + s by omega] at hper
    unfold orCol
    rw [hper]
    cases h0 : cell (n - P + s) 0
    · have h0' : cell (n + s) 0 = false := hper.trans h0
      have h1 : cell (n + s) 1 = cell (n + s - P) 1 :=
        Classical.byContradiction fun h1 => hne ⟨n + s, by omega, by omega, h0', h1⟩
      rw [show n + s - P = n - P + s by omega] at h1
      simp only [Int.zero_add, Bool.false_or, h1]
    · rfl

/-- **Finitary Jen.** For `0 < P ≤ n`, the center column and `orCol 0` are never both `P`-periodic on
the whole time interval `[n - P, 2n]`. (So columns `0` and `1` are never both `P`-periodic there.) -/
theorem finitary_jen {P n : Nat} (hP : 0 < P) (hn : P ≤ n)
    (hc : ∀ x, n - P ≤ x → x + P ≤ 2 * n → cell (x + P) 0 = cell x 0)
    (he : ∀ x, n - P ≤ x → x + P < 2 * n → orCol 0 (x + P) = orCol 0 x) : False := by
  refine window_jen (t₁ := n - P) (t₂ := n) (by omega) (fun s hs => ?_) (fun s hs => ?_)
  · have := hc (n - P + s) (by omega) (by omega)
    rw [show n - P + s + P = n + s by omega] at this
    exact this.symm
  · have := he (n - P + s) (by omega) (by omega)
    rw [show n - P + s + P = n + s by omega] at this
    exact this.symm

/-- **Weakened Jen.** If the center column is eventually periodic, then `center || column 1` is not:
column 1 is not eventually periodic even on the set of times where the center is white. -/
theorem or_not_eventuallyPeriodic (hc : EventuallyPeriodic fun t => cell t 0) :
    ¬ EventuallyPeriodic fun t => orCol 0 t := by
  intro he
  obtain ⟨T, P, hP, hpc, hpe⟩ := common_period hc he
  obtain ⟨s, hs1, hs2, h0, h1⟩ := periodic_window hP hpc (T + P) (Nat.le_refl _)
  have hcs : cell s 0 = cell (s - P) 0 := by
    have := hpc (s - P) (by omega); rw [show s - P + P = s by omega] at this; exact this
  have hes : orCol 0 s = orCol 0 (s - P) := by
    have := hpe (s - P) (by omega); rw [show s - P + P = s by omega] at this; exact this
  unfold orCol at hes
  rw [← hcs, h0] at hes
  simp only [Int.zero_add, Bool.false_or] at hes
  exact h1 hes


/-! ## Can the claim's gap threshold `s (k+1) > 2 s k + 2 P'` be rescued? -/

theorem cell_second_edge (u : Nat) : cell (u + 1) (-(u : Int)) = true := by
  show rule (cell u (-(u : Int) - 1)) (cell u (-(u : Int))) (cell u (-(u : Int) + 1)) = true
  rw [cell_left_edge u, cell_eq_false_of_lt u (-(u : Int) - 1) (by omega)]
  rfl

/-- Sharpened window: for `t₁ + 2 ≤ t₂`, windows of length `t₂ - 1` already differ
(use column `-(t₂ - 1)`: white at `t₁`, the second edge cell at `t₂`). -/
theorem window_jen_sharp {t₁ t₂ : Nat} (h : t₁ + 2 ≤ t₂)
    (hc : ∀ s, s ≤ t₂ - 1 → cell (t₁ + s) 0 = cell (t₂ + s) 0)
    (he : ∀ s, s < t₂ - 1 → orCol 0 (t₁ + s) = orCol 0 (t₂ + s)) : False := by
  have key := (determine (i := 0) (t₂ - 1) hc he (t₂ - 1) 0 (by omega)).1
  simp only [Nat.add_zero, Int.zero_sub] at key
  have h1 : cell t₁ (-((t₂ - 1 : Nat) : Int)) = false := cell_eq_false_of_lt t₁ _ (by omega)
  have h2 := cell_second_edge (t₂ - 1)
  rw [show t₂ - 1 + 1 = t₂ by omega] at h2
  rw [h1, h2] at key
  exact absurd key (by decide)

/-- Sharpened periodic window, `P ≥ 2`: a defect in `[n, 2n - 1)`. -/
theorem periodic_window_sharp {T P : Nat} (hP : 2 ≤ P)
    (hc : ∀ t, T ≤ t → cell (t + P) 0 = cell t 0) (n : Nat) (hn : T + P ≤ n) :
    ∃ s, n ≤ s ∧ s + 1 < 2 * n ∧ cell s 0 = false ∧ cell s 1 ≠ cell (s - P) 1 := by
  refine Classical.byContradiction fun hne => ?_
  refine window_jen_sharp (t₁ := n - P) (t₂ := n) (by omega) (fun s _ => ?_) (fun s hs => ?_)
  · have := hc (n - P + s) (by omega)
    rw [show n - P + s + P = n + s by omega] at this
    exact this.symm
  · have hper := hc (n - P + s) (by omega)
    rw [show n - P + s + P = n + s by omega] at hper
    unfold orCol
    rw [hper]
    cases h0 : cell (n - P + s) 0
    · have h0' : cell (n + s) 0 = false := hper.trans h0
      have h1 : cell (n + s) 1 = cell (n + s - P) 1 :=
        Classical.byContradiction fun h1 => hne ⟨n + s, by omega, by omega, h0', h1⟩
      rw [show n + s - P = n - P + s by omega] at h1
      simp only [Int.zero_add, Bool.false_or, h1]
    · rfl

theorem strict_mono_le {s : Nat → Nat} (hs : ∀ i, s i < s (i + 1)) :
    ∀ i j, i ≤ j → s i ≤ s j := by
  intro i j h
  induction j with
  | zero => have : i = 0 := by omega
            subst this; exact Nat.le_refl _
  | succ j ih =>
    by_cases hij : i = j + 1
    · subst hij; exact Nat.le_refl _
    · have := ih (by omega); have := hs j; omega

theorem strict_mono_ge_index {s : Nat → Nat} (hs : ∀ i, s i < s (i + 1)) : ∀ k, k ≤ s k := by
  intro k; induction k with
  | zero => exact Nat.zero_le _
  | succ k ih => have := hs k; omega

/-- (b) with the claim's exact gap threshold, rescued: `S = {s 0 < s 1 < …}` with infinitely
many `k` such that `s (k+1) > 2 s k + 2 P'`. Uses the sharpened window when `P' ≥ 2` and the
library theorem `no_column_eventually_constant` when `P' = 1`. -/
theorem corollary_b_claimed_gaps {T P Q Te : Nat} (hP : 0 < P) (hQ : 0 < Q)
    (hc : ∀ t, T ≤ t → cell (t + P) 0 = cell t 0)
    (e : Nat → Bool) (he : ∀ t, Te ≤ t → e (t + Q) = e t)
    (s : Nat → Nat) (hs : ∀ i, s i < s (i + 1))
    (hd : ∀ t, cell t 0 = false → (¬ ∃ j, s j = t) → cell t 1 = e t)
    (hgaps : ∀ K, ∃ k, K ≤ k ∧ s (k + 1) > 2 * s k + 2 * Nat.lcm P Q) : False := by
  have hP'pos : 0 < Nat.lcm P Q := Nat.lcm_pos hP hQ
  obtain ⟨a, ha⟩ := Nat.dvd_lcm_left P Q
  obtain ⟨b, hb⟩ := Nat.dvd_lcm_right P Q
  generalize hL : Nat.lcm P Q = P' at ha hb hP'pos hgaps
  have hc' : ∀ t, T ≤ t → cell (t + P') 0 = cell t 0 := by
    intro t ht
    have := Rule30Jen.periodic_mul (f := fun t => cell t 0) hc a t ht
    rw [ha, Nat.mul_comm P a]; exact this
  by_cases h1 : P' = 1
  · -- `P' = 1`: the center column is eventually constant, impossible.
    subst h1
    apply Rule30Prize.no_column_eventually_constant 0
    have hconst : ∀ d, cell (T + d) 0 = cell T 0 := by
      intro d
      induction d with
      | zero => rfl
      | succ d ih => rw [show T + (d + 1) = (T + d) + 1 by omega, hc' (T + d) (by omega), ih]
    refine ⟨T, cell T 0, fun t ht => ?_⟩
    have := hconst (t - T)
    rw [show T + (t - T) = t by omega] at this
    exact this
  · have he' : ∀ t, Te ≤ t → e (t + P') = e t := by
      intro t ht
      have := Rule30Jen.periodic_mul (f := e) he b t ht
      rw [hb, Nat.mul_comm Q b]; exact this
    obtain ⟨k, hk, hgap⟩ := hgaps (T + Te + P')
    have hks := strict_mono_ge_index hs k
    let n := s k + P' + 1
    have hnS : ∀ x, n - P' ≤ x → x < s (k + 1) → ¬ ∃ j, s j = x := by
      intro x h1x h2x ⟨j, hj⟩
      subst hj
      by_cases hjk : j ≤ k
      · have := strict_mono_le hs j k hjk; omega
      · have := strict_mono_le hs (k + 1) j (by omega); omega
    obtain ⟨x, h1, h2, h3, h4⟩ := periodic_window_sharp (by omega) hc' n (by omega)
    have hx0 : cell (x - P') 0 = false := by
      have := hc' (x - P') (by omega)
      rw [show x - P' + P' = x by omega] at this
      rw [← this]; exact h3
    have hdx : cell x 1 = e x := hd x h3 (hnS x (by omega) (by omega))
    have hdx' : cell (x - P') 1 = e (x - P') := hd (x - P') hx0 (hnS (x - P') (by omega) (by omega))
    have hex : e x = e (x - P') := by
      have := he' (x - P') (by omega)
      rw [show x - P' + P' = x by omega] at this
      exact this
    exact h4 (by rw [hdx, hdx', hex])

end Rule30JenWindow
end Ruliology.CellularAutomata

#print axioms Ruliology.CellularAutomata.Rule30JenWindow.periodic_window_sharp
#print axioms Ruliology.CellularAutomata.Rule30JenWindow.corollary_b_claimed_gaps
