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


/-! ## Adversarial verification of claim C3 (corollaries) -/

/-- (a), dyadic block form: every block `[2^j (T+P), 2^(j+1) (T+P))` contains a `P`-defect. -/
theorem corollary_a_block {T P : Nat} (hP : 0 < P)
    (hc : ∀ t, T ≤ t → cell (t + P) 0 = cell t 0) (j : Nat) :
    ∃ s, 2 ^ j * (T + P) ≤ s ∧ s < 2 ^ (j + 1) * (T + P) ∧
      cell s 0 = false ∧ cell s 1 ≠ cell (s - P) 1 := by
  have h1 : T + P ≤ 2 ^ j * (T + P) := by
    have : 1 ≤ 2 ^ j := Nat.one_le_two_pow
    calc T + P = 1 * (T + P) := by omega
      _ ≤ 2 ^ j * (T + P) := Nat.mul_le_mul_right _ this
  obtain ⟨s, h1s, h2s, h3s, h4s⟩ := periodic_window hP hc (2 ^ j * (T + P)) h1
  have e : 2 ^ (j + 1) * (T + P) = 2 * (2 ^ j * (T + P)) := by
    rw [Nat.pow_succ, Nat.mul_comm (2 ^ j) 2, Nat.mul_assoc]
  exact ⟨s, h1s, by rw [e]; exact h2s, h3s, h4s⟩

/-- (a), counting form: if `2^J (T+P) ≤ N` there are `J` distinct `P`-defects below `N`
(a strictly increasing choice `f 0 < f 1 < … < f (J-1)`). -/
theorem corollary_a {T P : Nat} (hP : 0 < P)
    (hc : ∀ t, T ≤ t → cell (t + P) 0 = cell t 0) (J N : Nat) (hJN : 2 ^ J * (T + P) ≤ N) :
    ∃ f : Nat → Nat, (∀ j, j < J → f j < N ∧ cell (f j) 0 = false ∧ cell (f j) 1 ≠ cell (f j - P) 1)
      ∧ (∀ i j, i < j → f i < f j) := by
  let f : Nat → Nat := fun j => Classical.choose (corollary_a_block hP hc j)
  have hf : ∀ j, 2 ^ j * (T + P) ≤ f j ∧ f j < 2 ^ (j + 1) * (T + P) ∧
      cell (f j) 0 = false ∧ cell (f j) 1 ≠ cell (f j - P) 1 :=
    fun j => Classical.choose_spec (corollary_a_block hP hc j)
  have mono : ∀ a b, a ≤ b → 2 ^ a * (T + P) ≤ 2 ^ b * (T + P) := fun a b h =>
    Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide) h)
  refine ⟨f, fun j hj => ⟨?_, (hf j).2.2⟩, fun i j hij => ?_⟩
  · have := (hf j).2.1; have := mono (j + 1) J (by omega); omega
  · have := (hf i).2.1; have := (hf j).1; have := mono (i + 1) j (by omega); omega

/-- (b) with any positive common multiple `P'` of `P` and `Q` (covers `P' = lcm P Q`). -/
theorem corollary_b {T P Q Te P' : Nat} (hP' : 0 < P') (hPd : P ∣ P') (hQd : Q ∣ P')
    (hc : ∀ t, T ≤ t → cell (t + P) 0 = cell t 0)
    (e : Nat → Bool) (he : ∀ t, Te ≤ t → e (t + Q) = e t)
    (S : Nat → Prop)
    (hd : ∀ t, cell t 0 = false → ¬ S t → cell t 1 = e t)
    (hS : ∀ N, ∃ n, N ≤ n ∧ ∀ x, n - P' ≤ x → x < 2 * n → ¬ S x) : False := by
  obtain ⟨a, ha⟩ := hPd
  obtain ⟨b, hb⟩ := hQd
  have hc' : ∀ t, T ≤ t → cell (t + P') 0 = cell t 0 := by
    intro t ht
    have := periodic_mul (f := fun t => cell t 0) hc a t ht
    rw [ha, Nat.mul_comm P a]; exact this
  have he' : ∀ t, Te ≤ t → e (t + P') = e t := by
    intro t ht
    have := periodic_mul (f := e) he b t ht
    rw [hb, Nat.mul_comm Q b]; exact this
  obtain ⟨n, hn, hgap⟩ := hS (T + Te + P')
  obtain ⟨s, h1, h2, h3, h4⟩ := periodic_window hP' hc' n (by omega)
  have hs0 : cell (s - P') 0 = false := by
    have := hc' (s - P') (by omega)
    rw [show s - P' + P' = s by omega] at this
    rw [← this]; exact h3
  have hdS : cell s 1 = e s := hd s h3 (hgap s (by omega) h2)
  have hdS' : cell (s - P') 1 = e (s - P') :=
    hd (s - P') hs0 (hgap (s - P') (by omega) (by omega))
  have hes : e s = e (s - P') := by
    have := he' (s - P') (by omega)
    rw [show s - P' + P' = s by omega] at this
    exact this
  exact h4 (by rw [hdS, hdS', hes])

/-- The `lcm` instance of (b). -/
theorem corollary_b_lcm {T P Q Te : Nat} (hP : 0 < P) (hQ : 0 < Q)
    (hc : ∀ t, T ≤ t → cell (t + P) 0 = cell t 0)
    (e : Nat → Bool) (he : ∀ t, Te ≤ t → e (t + Q) = e t)
    (S : Nat → Prop)
    (hd : ∀ t, cell t 0 = false → ¬ S t → cell t 1 = e t)
    (hS : ∀ N, ∃ n, N ≤ n ∧ ∀ x, n - Nat.lcm P Q ≤ x → x < 2 * n → ¬ S x) : False :=
  corollary_b (Nat.lcm_pos hP hQ) (Nat.dvd_lcm_left P Q) (Nat.dvd_lcm_right P Q) hc e he S hd hS

/-- Coverage, finite `S`. -/
theorem cover_finite (P' : Nat) (S : Nat → Prop) (hfin : ∃ M, ∀ x, S x → x < M) :
    ∀ N, ∃ n, N ≤ n ∧ ∀ x, n - P' ≤ x → x < 2 * n → ¬ S x := by
  obtain ⟨M, hM⟩ := hfin
  intro N
  exact ⟨N + M + P', by omega, fun x h1 _ hx => by have := hM x hx; omega⟩

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

/-- Coverage, gaps, CORRECTED threshold `s (k+1) ≥ 2 s k + 2 P' + 2`. -/
theorem cover_gaps_corrected (P' : Nat) (s : Nat → Nat) (hs : ∀ i, s i < s (i + 1))
    (hgaps : ∀ K, ∃ k, K ≤ k ∧ 2 * s k + 2 * P' + 2 ≤ s (k + 1)) :
    ∀ N, ∃ n, N ≤ n ∧ ∀ x, n - P' ≤ x → x < 2 * n → ¬ (∃ j, s j = x) := by
  intro N
  obtain ⟨k, hk, hgap⟩ := hgaps N
  have hks := strict_mono_ge_index hs k
  refine ⟨s k + P' + 1, by omega, fun x h1 h2 ⟨j, hj⟩ => ?_⟩
  subst hj
  by_cases hjk : j ≤ k
  · have := strict_mono_le hs j k hjk; omega
  · have := strict_mono_le hs (k + 1) j (by omega); omega

/-- The claim's threshold `s (k+1) > 2 s k + 2 P'` is NOT enough: this `S` satisfies it at every
gap, but meets `[n - P', 2n)` for every `n ≥ 1`. -/
def sx (P' : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => 2 * sx P' k + 2 * P' + 1

theorem sx_gap (P' k : Nat) : sx P' (k + 1) > 2 * sx P' k + 2 * P' := by
  simp only [sx]; omega

theorem sx_strict (P' i : Nat) : sx P' i < sx P' (i + 1) := by
  simp only [sx]; omega

theorem sx_cover (P' : Nat) : ∀ k n, 1 ≤ n → n ≤ sx P' k + P' →
    ∃ j, n - P' ≤ sx P' j ∧ sx P' j < 2 * n
  | 0, n, h1, h2 => ⟨0, by simp only [sx] at h2 ⊢; omega⟩
  | k + 1, n, h1, h2 => by
    by_cases h : n ≤ sx P' k + P'
    · exact sx_cover P' k n h1 h
    · exact ⟨k + 1, by simp only [sx] at h2 ⊢; omega, by simp only [sx]; omega⟩

theorem sx_not_cover (P' : Nat) :
    ¬ (∀ N, ∃ n, N ≤ n ∧ ∀ x, n - P' ≤ x → x < 2 * n → ¬ (∃ k, sx P' k = x)) := by
  intro hS
  obtain ⟨n, hn, hgap⟩ := hS 1
  obtain ⟨j, hj1, hj2⟩ := sx_cover P' n n hn
    (by have := strict_mono_ge_index (sx_strict P') n; omega)
  exact hgap (sx P' j) hj1 hj2 ⟨j, rfl⟩

end Rule30JenWindow
end Ruliology.CellularAutomata

#print axioms Ruliology.CellularAutomata.Rule30JenWindow.window_jen
#print axioms Ruliology.CellularAutomata.Rule30JenWindow.periodic_window
#print axioms Ruliology.CellularAutomata.Rule30JenWindow.corollary_a
#print axioms Ruliology.CellularAutomata.Rule30JenWindow.corollary_b_lcm
#print axioms Ruliology.CellularAutomata.Rule30JenWindow.cover_gaps_corrected
#print axioms Ruliology.CellularAutomata.Rule30JenWindow.sx_not_cover
