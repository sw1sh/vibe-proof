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

/-! ### Nine black cells in a column force the next two cells to the right -/

/-- One step of the cells to the right of a column, given the column's value `a`: the head's left
neighbour is `a`. The result is one cell shorter, since the last cell's right neighbour is unknown. -/
def stepList : Bool → List Bool → List Bool
  | _, [] => []
  | _, [_] => []
  | a, b :: c :: rest => rule a b c :: stepList b (c :: rest)

/-- `r` steps of `stepList` next to a column that stays black. -/
def stepsTrue : Nat → List Bool → List Bool
  | 0, l => l
  | r + 1, l => stepsTrue r (stepList true l)

/-- `[cell t (j + 1), …, cell t (j + n)]`. -/
def rowList (t : Nat) (j : Int) : Nat → List Bool
  | 0 => []
  | n + 1 => cell t (j + 1) :: rowList t (j + 1) n

theorem rowList_length (t : Nat) : ∀ (n : Nat) (j : Int), (rowList t j n).length = n
  | 0, _ => rfl
  | n + 1, j => by simp [rowList, rowList_length t n (j + 1)]

theorem step_rowList (t : Nat) : ∀ (n : Nat) (j : Int),
    stepList (cell t j) (rowList t j (n + 1)) = rowList (t + 1) j n
  | 0, _ => rfl
  | n + 1, j => by
    have h1 : cell (t + 1) (j + 1) = rule (cell t j) (cell t (j + 1)) (cell t (j + 1 + 1)) := by
      show rule (cell t (j + 1 - 1)) (cell t (j + 1)) (cell t (j + 1 + 1)) = _
      rw [show j + 1 - 1 = j by omega]
    have h2 := step_rowList t n (j + 1)
    show stepList (cell t j) (cell t (j + 1) :: cell t (j + 1 + 1) :: rowList t (j + 1 + 1) n) =
      cell (t + 1) (j + 1) :: rowList (t + 1) (j + 1) n
    rw [h1, ← h2]
    rfl

theorem stepsTrue_rowList (j : Int) (n : Nat) :
    ∀ r t, (∀ s, s < r → cell (t + s) j = true) →
      stepsTrue r (rowList t j (n + r)) = rowList (t + r) j n
  | 0, t, _ => rfl
  | r + 1, t, h => by
    have h0 : cell t j = true := by simpa using h 0 (by omega)
    have hs : stepList true (rowList t j (n + r + 1)) = rowList (t + 1) j (n + r) := by
      rw [← step_rowList t (n + r) j, h0]
    show stepsTrue r (stepList true (rowList t j (n + r + 1))) = _
    rw [hs, stepsTrue_rowList j n r (t + 1) (fun s hs => by
      rw [show t + 1 + s = t + (s + 1) by omega]; exact h (s + 1) (by omega)),
      show t + 1 + r = t + (r + 1) by omega]

/-- The finite check: after nine steps next to a black column, every 11-cell row ends as
`[white, black]`. -/
theorem nine_ones_check :
    (allLists 11).all (fun l => decide (stepsTrue 9 l = [false, true])) = true := by decide +kernel

/-- **Nine black cells force white, black.** If column `j` is black at times `t, …, t + 8`, then at
time `t + 9` column `j + 1` is white and column `j + 2` is black. -/
theorem nine_ones {t : Nat} {j : Int} (h : ∀ s, s < 9 → cell (t + s) j = true) :
    cell (t + 9) (j + 1) = false ∧ cell (t + 9) (j + 1 + 1) = true := by
  have hrow := stepsTrue_rowList j 2 9 t h
  have hmem : rowList t j (2 + 9) ∈ allLists 11 := by
    have := mem_allLists (rowList t j (2 + 9)); rwa [rowList_length] at this
  have hcheck := List.all_eq_true.mp nine_ones_check _ hmem
  have hfin : stepsTrue 9 (rowList t j (2 + 9)) = [false, true] := of_decide_eq_true hcheck
  rw [hrow] at hfin
  change cell (t + 9) (j + 1) :: cell (t + 9) (j + 1 + 1) :: [] = [false, true] at hfin
  injection hfin with h1 h2
  injection h2 with h2 _
  exact ⟨h1, h2⟩

/-! ### Weakened Jen for any column -/

/-- **Weakened Jen, any column.** If column `i` is eventually periodic, `orCol i` is not. (Column
`i - 1` is `cell (t + 1) i xor orCol i t`, so it would be eventually periodic too.) -/
theorem or_not_eventuallyPeriodic_col (i : Int) (hc : EventuallyPeriodic fun t => cell t i) :
    ¬ EventuallyPeriodic fun t => orCol i t := by
  intro he
  obtain ⟨T, P, hP, hpc, hpe⟩ := common_period hc he
  refine not_adjacent (i - 1) ⟨T, P, hP, fun t ht => ?_⟩ (by rw [show i - 1 + 1 = i by omega]; exact hc)
  show cell (t + P) (i - 1) = cell t (i - 1)
  rw [cell_left', cell_left', show t + P + 1 = (t + 1) + P by omega]
  have h1 : cell ((t + 1) + P) i = cell (t + 1) i := hpc (t + 1) (by omega)
  have h2 : orCol i (t + P) = orCol i t := hpe t ht
  rw [h1, h2]

/-! ### Long runs of black cells -/

/-- A white run of column `i` right after nine black cells: column `i + 1` is white at the first
white cell and black at the later ones. -/
theorem col_in_white_run' (i : Int) :
    ∀ k u, (∀ s, s < 9 → cell (u + s) i = true) → (∀ j, j ≤ k → cell (u + 9 + j) i = false) →
      cell (u + 9 + k) (i + 1) = decide (k ≠ 0) ∧ (k = 0 → cell (u + 9) (i + 1 + 1) = true) := by
  intro k
  induction k with
  | zero =>
    intro u h9s hz
    have h9 := nine_ones (j := i) h9s
    exact ⟨h9.1, fun _ => h9.2⟩
  | succ k ih =>
    intro u h9s hz
    refine ⟨?_, fun h => absurd h (by omega)⟩
    have hk0 : cell (u + 9 + k) i = false := hz k (by omega)
    have hstep : cell (u + 9 + (k + 1)) (i + 1) =
        rule (cell (u + 9 + k) i) (cell (u + 9 + k) (i + 1)) (cell (u + 9 + k) (i + 1 + 1)) := by
      show rule (cell (u + 9 + k) (i + 1 - 1)) (cell (u + 9 + k) (i + 1)) (cell (u + 9 + k) (i + 1 + 1)) = _
      rw [show i + 1 - 1 = i by omega]
    have ih' := ih u h9s (fun j hj => hz j (by omega))
    rw [hstep, hk0]
    cases k with
    | zero =>
      have e1 : cell (u + 9 + 0) (i + 1) = false := ih'.1
      have e2 : cell (u + 9) (i + 1 + 1) = true := ih'.2 rfl
      rw [e1, show u + 9 + 0 = u + 9 from rfl, e2]
      rfl
    | succ k =>
      rw [ih'.1]
      rfl

/-- Inside a white run of column `i` that starts right after nine black cells, column `i + 1` is
white at the first white cell and black at the later ones. -/
theorem col_in_white_run (i : Int) {T : Nat}
    (hruns : ∀ u, T ≤ u → cell (u + 9) i = false → cell (u + 8) i = true →
      ∀ s, s < 9 → cell (u + s) i = true) :
    ∀ k u, T ≤ u → cell (u + 8) i = true → (∀ j, j ≤ k → cell (u + 9 + j) i = false) →
      cell (u + 9 + k) (i + 1) = decide (k ≠ 0) ∧ (k = 0 → cell (u + 9) (i + 1 + 1) = true) :=
  fun k u hu h8 hz => col_in_white_run' i k u (hruns u hu (hz 0 (by omega)) h8) hz

/-- Trailing white cells: either the last `n + 1` values of `f` before and at `t` are all white, or
there is a black cell right before a white run ending at `t` of length at most `n`. -/
theorem trailing (f : Nat → Bool) (t : Nat) (h0 : f t = false) :
    ∀ n, (∀ j, j ≤ n → f (t - j) = false) ∨
      ∃ k, k < n ∧ f (t - (k + 1)) = true ∧ ∀ j, j ≤ k → f (t - j) = false := by
  intro n
  induction n with
  | zero => exact Or.inl fun j hj => by rw [show j = 0 by omega]; simpa using h0
  | succ n ih =>
    rcases ih with h | ⟨k, hk, h1, h2⟩
    · cases hf : f (t - (n + 1))
      · exact Or.inl fun j hj => by
          rcases Nat.lt_or_ge j (n + 1) with hj' | hj'
          · exact h j (by omega)
          · rw [show j = n + 1 by omega]; exact hf
      · exact Or.inr ⟨n, by omega, hf, h⟩
    · exact Or.inr ⟨k, by omega, h1, h2⟩

/-- **Long black runs exclude periodicity, any column.** Suppose that from time `T` on, every black run
of column `i` that is followed by a white cell has length at least `9`. Then column `i` is not
eventually periodic. -/
theorem not_eventuallyPeriodic_of_long_one_runs_col (i : Int) {T : Nat}
    (hruns : ∀ u, T ≤ u → cell (u + 9) i = false → cell (u + 8) i = true →
      ∀ s, s < 9 → cell (u + s) i = true) :
    ¬ EventuallyPeriodic fun t => cell t i := by
  intro hc
  obtain ⟨T₀, P, hP, hper⟩ := hc
  have hper' : ∀ t, T₀ ≤ t → cell (t + P) i = cell t i := hper
  by_cases hw : ∃ t, T₀ ≤ t ∧ ∀ s, s < P → cell (t + s) i = false
  · -- a white period window: column `i` is eventually white
    obtain ⟨t, ht, hs⟩ := hw
    have hk : ∀ k s, s < P → cell (t + k * P + s) i = false := by
      intro k
      induction k with
      | zero => intro s hs'; simpa using hs s hs'
      | succ k ih =>
        intro s hs'
        rw [show t + (k + 1) * P + s = (t + k * P + s) + P by rw [Nat.succ_mul]; omega,
          hper' _ (by omega)]
        exact ih s hs'
    refine Rule30Prize.no_column_eventually_constant i ⟨t, false, fun u hu => ?_⟩
    have := hk ((u - t) / P) ((u - t) % P) (Nat.mod_lt _ hP)
    rwa [show t + (u - t) / P * P + (u - t) % P = u by
      have := Nat.div_add_mod (u - t) P; rw [Nat.mul_comm] at this; omega] at this
  · -- every period window after `T₀` contains a black cell
    have hblack : ∀ t, T₀ ≤ t → ∃ s, s < P ∧ cell (t + s) i = true := by
      intro t ht
      refine Classical.byContradiction fun hne => hw ⟨t, ht, fun s hs => ?_⟩
      cases h : cell (t + s) i
      · rfl
      · exact absurd ⟨s, hs, h⟩ hne
    let B := T + T₀ + P + 10
    have hform : ∀ t, B ≤ t → orCol i t = (cell t i || !cell (t - 1) i) := by
      intro t ht
      cases h0 : cell t i
      · rcases trailing (fun u => cell u i) t h0 P with hall | ⟨k, hk, h1, h2⟩
        · obtain ⟨s, hs, hb⟩ := hblack (t - P) (by omega)
          have := hall (P - s) (by omega)
          rw [show t - (P - s) = t - P + s by omega, hb] at this
          exact absurd this (by decide)
        · have hrun := col_in_white_run i hruns k (t - (k + 1) - 8) (by omega)
            (by rw [show t - (k + 1) - 8 + 8 = t - (k + 1) by omega]; exact h1)
            (fun j hj => by
              rw [show t - (k + 1) - 8 + 9 + j = t - (k - j) by omega]; exact h2 (k - j) (by omega))
          rw [show t - (k + 1) - 8 + 9 + k = t by omega] at hrun
          unfold orCol
          rw [h0, Bool.false_or, Bool.false_or, hrun.1]
          cases k with
          | zero =>
            have : cell (t - 1) i = true := by simpa using h1
            rw [this]; rfl
          | succ k =>
            have : cell (t - 1) i = false := by simpa using h2 1 (by omega)
            rw [this]; rfl
      · unfold orCol; rw [h0]; rfl
    refine or_not_eventuallyPeriodic_col i ⟨T₀, P, hP, hper⟩ ⟨B, P, hP, fun t ht => ?_⟩
    show orCol i (t + P) = orCol i t
    rw [hform t (by omega), hform (t + P) (by omega), hper' t (by omega),
      show t + P - 1 = (t - 1) + P by omega, hper' (t - 1) (by omega)]

/-- **Long black runs exclude periodicity of the center column.** If from some time on every black
run of the center column that is followed by a white cell has length at least `9`, the center column is
not eventually periodic. Equivalently: an eventually periodic center column would have black runs of
length `1, …, 8` followed by white infinitely often. -/
theorem not_eventuallyPeriodic_of_long_one_runs {T : Nat}
    (hruns : ∀ u, T ≤ u → cell (u + 9) 0 = false → cell (u + 8) 0 = true →
      ∀ s, s < 9 → cell (u + s) 0 = true) :
    ¬ EventuallyPeriodic fun t => cell t 0 :=
  not_eventuallyPeriodic_of_long_one_runs_col 0 hruns

/-- **Finitary long-runs theorem.** Let `n ≥ a + 2P + 10`. The center column cannot, on the whole
interval `[a, 2n]`, be `P`-periodic, have a black cell in every window of length `P`, and have all its
black runs that are followed by a white cell of length at least `9`. So such a periodic stretch that
starts at time `a` is shorter than `a + 4P + 20`. -/
theorem finitary_long_runs {P a n : Nat} (hP : 0 < P) (hn : a + 2 * P + 10 ≤ n)
    (hper : ∀ x, a ≤ x → x + P ≤ 2 * n → cell (x + P) 0 = cell x 0)
    (hblack : ∀ x, a ≤ x → x + P ≤ 2 * n → ∃ s, s < P ∧ cell (x + s) 0 = true)
    (hruns : ∀ u, a ≤ u → u + 9 ≤ 2 * n → cell (u + 9) 0 = false → cell (u + 8) 0 = true →
      ∀ s, s < 9 → cell (u + s) 0 = true) : False := by
  have hform : ∀ x, a + P + 10 ≤ x → x ≤ 2 * n → orCol 0 x = (cell x 0 || !cell (x - 1) 0) := by
    intro x hx1 hx2
    cases h0 : cell x 0
    · rcases trailing (fun u => cell u 0) x h0 P with hall | ⟨k, hk, h1, h2⟩
      · obtain ⟨s, hs, hb⟩ := hblack (x - P) (by omega) (by omega)
        have := hall (P - s) (by omega)
        rw [show x - (P - s) = x - P + s by omega, hb] at this
        exact absurd this (by decide)
      · have h9s := hruns (x - (k + 1) - 8) (by omega) (by omega)
          (by rw [show x - (k + 1) - 8 + 9 = x - k by omega]; exact h2 k (by omega))
          (by rw [show x - (k + 1) - 8 + 8 = x - (k + 1) by omega]; exact h1)
        have hrun := col_in_white_run' 0 k (x - (k + 1) - 8) h9s
          (fun j hj => by
            rw [show x - (k + 1) - 8 + 9 + j = x - (k - j) by omega]; exact h2 (k - j) (by omega))
        rw [show x - (k + 1) - 8 + 9 + k = x by omega] at hrun
        unfold orCol
        rw [h0, Bool.false_or, Bool.false_or, hrun.1]
        cases k with
        | zero =>
          have : cell (x - 1) 0 = true := by simpa using h1
          rw [this]; rfl
        | succ k =>
          have : cell (x - 1) 0 = false := by simpa using h2 1 (by omega)
          rw [this]; rfl
    · unfold orCol; rw [h0]; rfl
  refine window_jen (t₁ := n - P) (t₂ := n) (by omega) (fun s hs => ?_) (fun s hs => ?_)
  · have := hper (n - P + s) (by omega) (by omega)
    rw [show n - P + s + P = n + s by omega] at this
    exact this.symm
  · rw [hform (n - P + s) (by omega) (by omega), hform (n + s) (by omega) (by omega)]
    have e1 := hper (n - P + s) (by omega) (by omega)
    have e2 := hper (n - P + s - 1) (by omega) (by omega)
    rw [show n - P + s + P = n + s by omega] at e1
    rw [show n - P + s - 1 + P = n + s - 1 by omega] at e2
    rw [e1, e2]

/-! ### General forcing blocks and word certificates -/

/-- Steps of the cells to the right of a column whose values over time are `u`. -/
def stepsCol : List Bool → List Bool → List Bool
  | [], l => l
  | a :: u, l => stepsCol u (stepList a l)

theorem stepsCol_rowList (j : Int) (n : Nat) :
    ∀ (u : List Bool) (t : Nat), (∀ s, s < u.length → cell (t + s) j = u.getD s false) →
      stepsCol u (rowList t j (n + u.length)) = rowList (t + u.length) j n
  | [], t, _ => rfl
  | a :: u, t, h => by
    have h0 : cell t j = a := by simpa using h 0 (by simp)
    have hs : stepList a (rowList t j (n + u.length + 1)) = rowList (t + 1) j (n + u.length) := by
      rw [← step_rowList t (n + u.length) j, h0]
    show stepsCol u (stepList a (rowList t j (n + u.length + 1))) = _
    rw [hs, stepsCol_rowList j n u (t + 1) (fun s hs' => by
      have := h (s + 1) (by simp; omega)
      rw [show t + (s + 1) = t + 1 + s by omega] at this
      simpa using this)]
    simp only [List.length_cons]
    rw [show t + 1 + u.length = t + (u.length + 1) by omega]

/-- `u` forces the value `b`: for every row of `u.length + 1` cells next to a column with values `u`,
the first cell after `u.length` steps is `b`. -/
def forces (u : List Bool) (b : Bool) : Bool :=
  (allLists (u.length + 1)).all fun l => decide (stepsCol u l = [b])

/-- **Forcing lemma.** If `forces u b`, then whenever column `j` carries the block `u` on
`[t, t + u.length)`, the cell `(t + u.length, j + 1)` is `b`. -/
theorem forcing {u : List Bool} {b : Bool} (hf : forces u b = true) {t : Nat} {j : Int}
    (h : ∀ s, s < u.length → cell (t + s) j = u.getD s false) : cell (t + u.length) (j + 1) = b := by
  have hrow := stepsCol_rowList j 1 u t h
  rw [show 1 + u.length = u.length + 1 from Nat.add_comm _ _] at hrow
  have hmem : rowList t j (u.length + 1) ∈ allLists (u.length + 1) := by
    have := mem_allLists (rowList t j (u.length + 1)); rwa [rowList_length] at this
  have hfin : stepsCol u (rowList t j (u.length + 1)) = [b] :=
    of_decide_eq_true (List.all_eq_true.mp hf _ hmem)
  rw [hrow] at hfin
  change cell (t + u.length) (j + 1) :: [] = [b] at hfin
  injection hfin

/-- The `n` letters of `w^∞` just before phase `φ`. -/
def blockBefore (w : List Bool) (n φ : Nat) : List Bool :=
  (List.range n).map fun i => w.getD ((φ + n * w.length - n + i) % w.length) false

/-- The value forced at phase `φ` (read off one row; `forces` checks it for all rows). -/
def forcedVal (w : List Bool) (n φ : Nat) : Bool :=
  (stepsCol (blockBefore w n φ) (List.replicate (n + 1) false)).headD false

/-- **Word certificate**: every white phase of `w` is forced by the `n` letters before it. -/
def wordCert (w : List Bool) (n : Nat) : Bool :=
  (List.range w.length).all fun φ =>
    w.getD φ false || forces (blockBefore w n φ) (forcedVal w n φ)

theorem blockBefore_length (w : List Bool) (n φ : Nat) : (blockBefore w n φ).length = n := by
  simp [blockBefore]

/-- **Certified words are excluded.** If `wordCert w n`, the center column is not eventually equal
to `w` repeated (in any phase: the phase is absorbed into `T`). -/
theorem not_eventually_word (w : List Bool) (n : Nat) (hw : 0 < w.length)
    (hcert : wordCert w n = true) :
    ¬ ∃ T, ∀ t, T ≤ t → cell t 0 = w.getD ((t - T) % w.length) false := by
  rintro ⟨T, hT⟩
  have hcper : ∀ t, T ≤ t → cell (t + w.length) 0 = cell t 0 := by
    intro t ht
    rw [hT t ht, hT (t + w.length) (by omega), show t + w.length - T = (t - T) + w.length by omega,
      Nat.add_mod_right]
  -- the value of `orCol 0` at a time is a function of its phase, from `T + n * w.length + n` on
  let g : Nat → Bool := fun φ => w.getD φ false || forcedVal w n φ
  have hform : ∀ t, T + n * w.length + n ≤ t → orCol 0 t = g ((t - T) % w.length) := by
    intro t ht
    have hφ : (t - T) % w.length < w.length := Nat.mod_lt _ hw
    have hc := List.all_eq_true.mp hcert ((t - T) % w.length) (List.mem_range.mpr hφ)
    unfold orCol g
    rw [hT t (by omega)]
    cases hwφ : w.getD ((t - T) % w.length) false
    · simp only [hwφ, Bool.false_or] at hc
      simp only [Int.zero_add, Bool.false_or]
      -- arithmetic facts about the phase
      have hd : (t - T) / w.length * w.length + (t - T) % w.length = t - T := by
        have := Nat.div_add_mod (t - T) w.length; rw [Nat.mul_comm] at this; exact this
      have hq : n ≤ (t - T) / w.length := (Nat.le_div_iff_mul_le hw).2 (by omega)
      have hA : n * w.length ≤ (t - T) / w.length * w.length := Nat.mul_le_mul_right _ hq
      have hB : n ≤ n * w.length := Nat.le_mul_of_pos_right n hw
      have hC : ((t - T) / w.length - n) * w.length = (t - T) / w.length * w.length - n * w.length :=
        Nat.sub_mul _ _ _
      have key := forcing (t := t - n) (j := 0) hc (fun s hs => by
        rw [blockBefore_length] at hs
        rw [hT (t - n + s) (by omega)]
        simp only [blockBefore, List.getD_eq_getElem?_getD, List.getElem?_map,
          List.getElem?_range hs, Option.map_some, Option.getD_some]
        congr 1
        have e1 : t - n + s - T = (t - T) % w.length + n * w.length - n + s +
            ((t - T) / w.length - n) * w.length := by
          omega
        rw [e1, Nat.add_mul_mod_self_right])
      rw [blockBefore_length, show t - n + n = t by omega] at key
      simpa using key
    · rfl
  refine or_not_eventuallyPeriodic ⟨T, w.length, hw, hcper⟩
    ⟨T + n * w.length + n, w.length, hw, fun t ht => ?_⟩
  show orCol 0 (t + w.length) = orCol 0 t
  rw [hform t ht, hform (t + w.length) (by omega), show t + w.length - T = (t - T) + w.length by omega,
    Nat.add_mod_right]

/-! ### Strip certificates with bitmask sets

A strip of `K` cells to the right of column `j` is encoded as a number `r < 2 ^ K` whose bit `k` is
`cell t (j + 1 + k)`. One step needs the column's value (left boundary) and the cell just right of
the strip (right boundary, unknown: both values are allowed). Sets of strip states are bitmasks.
Starting from all states and applying the driver word, the reachable sets over-approximate the true
strip states; if column `j + 1` is constant on them at every white phase, `orCol` is eventually
periodic, which `or_not_eventuallyPeriodic` forbids. -/

theorem testBit_toNat (b : Bool) (i : Nat) : b.toNat.testBit i = (decide (i = 0) && b) := by
  cases b <;> cases i <;> simp [Bool.toNat, Nat.testBit_succ]

/-- Strip encoding: `r < 2 ^ K` and bit `k < K` of `r` is `cell t (j + 1 + k)`. -/
def Enc (K t : Nat) (j : Int) (r : Nat) : Prop :=
  r < 2 ^ K ∧ ∀ k, k < K → r.testBit k = cell t (j + 1 + k)

/-- One step of a `K`-cell strip with left boundary `a` and right boundary `z`. -/
def stripStep (K : Nat) (a z : Bool) (r : Nat) : Nat :=
  (((r <<< 1) ||| a.toNat) ^^^ (r ||| (r >>> 1) ||| (z.toNat <<< (K - 1)))) % 2 ^ K

theorem stripStep_lt (K : Nat) (a z : Bool) (r : Nat) : stripStep K a z r < 2 ^ K :=
  Nat.mod_lt _ (Nat.two_pow_pos K)

theorem testBit_stripStep (K : Nat) (a z : Bool) (r : Nat) (hr : r < 2 ^ K) (k : Nat) (hk : k < K) :
    (stripStep K a z r).testBit k =
      rule (if k = 0 then a else r.testBit (k - 1)) (r.testBit k)
        (if k + 1 = K then z else r.testBit (k + 1)) := by
  unfold stripStep
  rw [Nat.testBit_mod_two_pow, Nat.testBit_xor, Nat.testBit_or, Nat.testBit_or, Nat.testBit_or,
    Nat.testBit_shiftLeft, Nat.testBit_shiftRight, Nat.testBit_shiftLeft, testBit_toNat, testBit_toNat,
    decide_eq_true hk, Bool.true_and, Nat.add_comm 1 k]
  unfold rule
  by_cases h0 : k = 0
  · subst h0
    by_cases h1 : 0 + 1 = K
    · have hb : r.testBit (0 + 1) = false := by
        rw [h1]; exact Nat.testBit_lt_two_pow hr
      simp only [if_pos h1, hb]
      simp [← h1]
    · simp only [if_neg h1]
      simp [show ¬ (0 ≥ K - 1) by omega]
  · by_cases h1 : k + 1 = K
    · have hb : r.testBit (k + 1) = false := by
        rw [h1]; exact Nat.testBit_lt_two_pow hr
      simp only [if_neg h0, if_pos h1, hb]
      simp [show k ≥ 1 by omega, show k ≥ K - 1 by omega, show k - (K - 1) = 0 by omega, h0]
    · simp only [if_neg h0, if_neg h1]
      simp [show k ≥ 1 by omega, show ¬ (k ≥ K - 1) by omega, h0]

theorem enc_step {K t : Nat} {j : Int} {r : Nat} (h : Enc K t j r) :
    Enc K (t + 1) j (stripStep K (cell t j) (cell t (j + 1 + K)) r) := by
  refine ⟨stripStep_lt _ _ _ _, fun k hk => ?_⟩
  rw [testBit_stripStep K _ _ r h.1 k hk]
  show _ = rule (cell t (j + 1 + (k : Int) - 1)) (cell t (j + 1 + k)) (cell t (j + 1 + k + 1))
  have hc : r.testBit k = cell t (j + 1 + k) := h.2 k hk
  have hl : (if k = 0 then cell t j else r.testBit (k - 1)) = cell t (j + 1 + (k : Int) - 1) := by
    split
    · rename_i h0; subst h0; congr 1; omega
    · rename_i h0; rw [h.2 (k - 1) (by omega)]; congr 1; omega
  have hr : (if k + 1 = K then cell t (j + 1 + K) else r.testBit (k + 1)) =
      cell t (j + 1 + k + 1) := by
    split
    · rename_i h1; congr 1; omega
    · rename_i h1; rw [h.2 (k + 1) (by omega)]; congr 1; omega
  rw [hl, hc, hr]

/-- The encoding of the actual strip. -/
def encRow (t : Nat) (j : Int) : Nat → Nat
  | 0 => 0
  | K + 1 => encRow t j K ||| ((cell t (j + 1 + K)).toNat <<< K)

theorem testBit_encRow (t : Nat) (j : Int) :
    ∀ K k, (encRow t j K).testBit k = (decide (k < K) && cell t (j + 1 + k))
  | 0, k => by simp [encRow]
  | K + 1, k => by
    rw [encRow, Nat.testBit_or, testBit_encRow t j K k, Nat.testBit_shiftLeft, testBit_toNat]
    by_cases hk : k < K
    · simp [hk, show k < K + 1 by omega, show ¬ K ≤ k by omega]
    · by_cases hk' : k = K
      · subst hk'; simp
      · simp [hk, show ¬ k < K + 1 by omega, show k - K ≠ 0 by omega]

theorem enc_encRow (K t : Nat) (j : Int) : Enc K t j (encRow t j K) := by
  refine ⟨Nat.lt_pow_two_of_testBit _ fun i hi => ?_, fun k hk => ?_⟩
  · rw [testBit_encRow]; simp [show ¬ i < K by omega]
  · rw [testBit_encRow]; simp [hk]

/-! Bitmask sets of strip states. -/

def imageAux (K : Nat) (a : Bool) (S : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => imageAux K a S n |||
      (if S.testBit n then (1 <<< stripStep K a false n) ||| (1 <<< stripStep K a true n) else 0)

/-- All successors of the states in `S`, for both values of the right boundary. -/
def image (K : Nat) (a : Bool) (S : Nat) : Nat := imageAux K a S (2 ^ K)

theorem testBit_one_shiftLeft (m i : Nat) : (1 <<< m).testBit i = decide (m = i) := by
  rw [Nat.one_shiftLeft, Nat.testBit_two_pow]

theorem mem_imageAux {K : Nat} {a : Bool} {S r : Nat} (hS : S.testBit r = true) (z : Bool) :
    ∀ n, r < n → (imageAux K a S n).testBit (stripStep K a z r) = true
  | 0, h => absurd h (Nat.not_lt_zero _)
  | n + 1, h => by
    rw [imageAux, Nat.testBit_or]
    by_cases hrn : r < n
    · rw [mem_imageAux hS z n hrn]; rfl
    · have : r = n := by omega
      subst this
      rw [if_pos hS, Nat.testBit_or, testBit_one_shiftLeft, testBit_one_shiftLeft]
      cases z <;> simp

theorem imageAux_mono {K : Nat} {a : Bool} {S S' : Nat}
    (hSS : ∀ s, S.testBit s = true → S'.testBit s = true) :
    ∀ n y, (imageAux K a S n).testBit y = true → (imageAux K a S' n).testBit y = true
  | 0, _, h => h
  | n + 1, y, h => by
    rw [imageAux, Nat.testBit_or] at h ⊢
    rcases Bool.or_eq_true_iff.mp h with h | h
    · rw [imageAux_mono hSS n y h]; rfl
    · by_cases hn : S.testBit n = true
      · rw [if_pos hn] at h
        rw [if_pos (hSS n hn), h]; simp
      · rw [if_neg hn, Nat.zero_testBit] at h; exact absurd h (by decide)

/-- Apply a driver word to a set of strip states. -/
def applyWord (K : Nat) : List Bool → Nat → Nat
  | [], S => S
  | a :: u, S => applyWord K u (image K a S)

theorem applyWord_mono (K : Nat) : ∀ (u : List Bool) {S S' : Nat},
    (∀ s, S.testBit s = true → S'.testBit s = true) →
      ∀ y, (applyWord K u S).testBit y = true → (applyWord K u S').testBit y = true
  | [], _, _, h => h
  | _ :: u, _, _, h => applyWord_mono K u (fun y => imageAux_mono h (2 ^ K) y)

/-- **Soundness of the strip sets.** If the actual strip is in `S` at time `t` and column `j` carries
the word `u` from `t` on, the actual strip at time `t + u.length` is in `applyWord K u S`. -/
theorem enc_applyWord {K : Nat} {j : Int} :
    ∀ (u : List Bool) (t r S : Nat), Enc K t j r → S.testBit r = true →
      (∀ s, s < u.length → cell (t + s) j = u.getD s false) →
      ∃ r', Enc K (t + u.length) j r' ∧ (applyWord K u S).testBit r' = true
  | [], t, r, S, he, hS, _ => ⟨r, he, hS⟩
  | a :: u, t, r, S, he, hS, hu => by
    have ha : cell t j = a := by simpa using hu 0 (by simp)
    have he1 := enc_step he
    rw [ha] at he1
    have hS1 : (image K a S).testBit (stripStep K a (cell t (j + 1 + K)) r) = true :=
      mem_imageAux hS _ (2 ^ K) he.1
    obtain ⟨r', he', hS'⟩ := enc_applyWord u (t + 1) _ _ he1 hS1 (fun s hs => by
      have := hu (s + 1) (by simp; omega)
      rw [show t + (s + 1) = t + 1 + s by omega] at this
      simpa using this)
    refine ⟨r', ?_, hS'⟩
    rw [show t + (a :: u).length = t + 1 + u.length by simp; omega]
    exact he'

/-- `k` repetitions of the word. -/
def iterW (K : Nat) (w : List Bool) : Nat → Nat → Nat
  | 0, S => S
  | k + 1, S => iterW K w k (applyWord K w S)

def allBelow (p : Nat → Bool) : Nat → Bool
  | 0 => true
  | n + 1 => allBelow p n && p n

theorem allBelow_spec {p : Nat → Bool} : ∀ {n}, allBelow p n = true → ∀ i, i < n → p i = true
  | 0, _, i, hi => absurd hi (Nat.not_lt_zero _)
  | n + 1, h, i, hi => by
    rw [allBelow, Bool.and_eq_true] at h
    by_cases hin : i < n
    · exact allBelow_spec h.1 i hin
    · rw [show i = n by omega]; exact h.2

/-- `S ⊆ S'` on states below `2 ^ K`. -/
def subsetB (K S S' : Nat) : Bool := allBelow (fun s => !S.testBit s || S'.testBit s) (2 ^ K)

/-- Column `j + 1` (bit `0`) equals `b` on every state of `S`. -/
def colConst (K S : Nat) (b : Bool) : Bool := allBelow (fun s => !S.testBit s || s.testBit 0 == b) (2 ^ K)

/-- All `2 ^ K` strip states. -/
def fullSet (K : Nat) : Nat := 2 ^ (2 ^ K) - 1

/-- **Strip certificate** for the word `w` at strip width `K` after `k` warm-up periods: the set `S0`
reached after `k` periods is mapped into itself by one more period, and at every white phase of `w`
column `j + 1` is constant on the corresponding set. -/
def stripCert (w : List Bool) (K k : Nat) : Bool :=
  let S0 := iterW K w k (fullSet K)
  subsetB K (applyWord K w S0) S0 &&
    (List.range w.length).all fun φ => w.getD φ false ||
      colConst K (applyWord K (w.take φ) S0) false || colConst K (applyWord K (w.take φ) S0) true

theorem enc_iterW {K : Nat} {j : Int} (w : List Bool) :
    ∀ (k t r S : Nat), Enc K t j r → S.testBit r = true →
      (∀ m s, m < k → s < w.length → cell (t + m * w.length + s) j = w.getD s false) →
      ∃ r', Enc K (t + k * w.length) j r' ∧ (iterW K w k S).testBit r' = true
  | 0, t, r, S, he, hS, _ => ⟨r, by simpa using he, hS⟩
  | k + 1, t, r, S, he, hS, hw => by
    obtain ⟨r1, he1, hS1⟩ := enc_applyWord w t r S he hS (fun s hs => by
      simpa using hw 0 s (by omega) hs)
    obtain ⟨r', he', hS'⟩ := enc_iterW w k (t + w.length) r1 _ he1 hS1 (fun m s hm hs => by
      rw [show t + w.length + m * w.length + s = t + (m + 1) * w.length + s by
        rw [Nat.succ_mul]; omega]
      exact hw (m + 1) s (by omega) hs)
    refine ⟨r', ?_, hS'⟩
    rw [show t + (k + 1) * w.length = t + w.length + k * w.length by rw [Nat.succ_mul]; omega]
    exact he'

/-- **Certified words are excluded.** If `stripCert w K k` holds, the center column is not eventually
equal to `w` repeated (in any phase). -/
theorem not_eventually_word_strip (w : List Bool) (K k : Nat) (hK : 1 ≤ K) (hw : 0 < w.length)
    (hcert : stripCert w K k = true) :
    ¬ ∃ T, ∀ t, T ≤ t → cell t 0 = w.getD ((t - T) % w.length) false := by
  rintro ⟨T, hT⟩
  unfold stripCert at hcert
  rw [Bool.and_eq_true] at hcert
  obtain ⟨hsub, hforce⟩ := hcert
  have hsub' := allBelow_spec hsub
  -- the driver is `w` on every period from `T`
  have hblock : ∀ m s, s < w.length → cell (T + m * w.length + s) 0 = w.getD s false := by
    intro m s hs
    rw [hT _ (by omega), show T + m * w.length + s - T = s + m * w.length by omega,
      Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hs]
  have hcper : ∀ t, T ≤ t → cell (t + w.length) 0 = cell t 0 := by
    intro t ht
    rw [hT t ht, hT (t + w.length) (by omega), show t + w.length - T = (t - T) + w.length by omega,
      Nat.add_mod_right]
  let S0 := iterW K w k (fullSet K)
  -- after `k` periods the strip is in `S0`
  have hstart : ∃ r, Enc K (T + k * w.length) 0 r ∧ S0.testBit r = true := by
    have h0 := enc_encRow K T 0
    have hfull : (fullSet K).testBit (encRow T 0 K) = true := by
      unfold fullSet; rw [Nat.testBit_two_pow_sub_one]; exact decide_eq_true h0.1
    exact enc_iterW w k T _ _ h0 hfull (fun m s _ hs => hblock m s hs)
  -- and it stays in `S0` at every later period start
  have hinv : ∀ m, ∃ r, Enc K (T + (k + m) * w.length) 0 r ∧ S0.testBit r = true := by
    intro m
    induction m with
    | zero => simpa using hstart
    | succ m ih =>
      obtain ⟨r, he, hS⟩ := ih
      obtain ⟨r', he', hS'⟩ := enc_applyWord w _ r S0 he hS (fun s hs => by
        rw [show T + (k + m) * w.length + s = T + (k + m) * w.length + s from rfl]
        exact hblock (k + m) s hs)
      refine ⟨r', ?_, ?_⟩
      · have hm : (k + (m + 1)) * w.length = (k + m) * w.length + w.length := by
          rw [show k + (m + 1) = (k + m) + 1 by omega, Nat.succ_mul]
        rw [hm, ← Nat.add_assoc]
        exact he'
      · have hlt : r' < 2 ^ K := he'.1
        have := hsub' r' hlt
        rw [hS', Bool.not_true, Bool.false_or] at this
        exact this
  -- the forced value at each white phase
  let g : Nat → Bool := fun φ => w.getD φ false ||
    !colConst K (applyWord K (w.take φ) S0) false
  have hform : ∀ t, T + k * w.length ≤ t → orCol 0 t = g ((t - T) % w.length) := by
    intro t ht
    have hφ : (t - T) % w.length < w.length := Nat.mod_lt _ hw
    have hdec : t = T + (k + ((t - T) / w.length - k)) * w.length + (t - T) % w.length := by
      have hd := Nat.div_add_mod (t - T) w.length
      have hq : k ≤ (t - T) / w.length := (Nat.le_div_iff_mul_le hw).2 (by omega)
      rw [show k + ((t - T) / w.length - k) = (t - T) / w.length by omega, Nat.mul_comm]
      omega
    obtain ⟨r, he, hS⟩ := hinv ((t - T) / w.length - k)
    obtain ⟨r', he', hS'⟩ := enc_applyWord (w.take ((t - T) % w.length)) _ r S0 he hS
      (fun s hs => by
        rw [List.length_take] at hs
        have hs' : s < (t - T) % w.length := by omega
        rw [hblock _ s (by omega)]
        simp [List.getD_eq_getElem?_getD, hs'])
    rw [List.length_take, Nat.min_eq_left (Nat.le_of_lt hφ), ← hdec] at he'
    have hcell : cell t 1 = r'.testBit 0 := by
      rw [he'.2 0 (by omega)]; rfl
    unfold orCol g
    rw [hT t (by omega)]
    simp only [Int.zero_add]
    have hfφ := List.all_eq_true.mp hforce ((t - T) % w.length) (List.mem_range.mpr hφ)
    cases hwφ : w.getD ((t - T) % w.length) false
    · rw [hwφ, Bool.false_or] at hfφ
      simp only [Bool.false_or]
      rw [hcell]
      cases hc0 : colConst K (applyWord K (w.take ((t - T) % w.length)) S0) false
      · rw [hc0, Bool.false_or] at hfφ
        have := allBelow_spec hfφ r' he'.1
        rw [hS', Bool.not_true, Bool.false_or, beq_iff_eq] at this
        rw [this]; rfl
      · have := allBelow_spec hc0 r' he'.1
        rw [hS', Bool.not_true, Bool.false_or, beq_iff_eq] at this
        rw [this]; rfl
    · rfl
  refine or_not_eventuallyPeriodic ⟨T, w.length, hw, hcper⟩
    ⟨T + k * w.length, w.length, hw, fun t ht => ?_⟩
  show orCol 0 (t + w.length) = orCol 0 t
  rw [hform t ht, hform (t + w.length) (by omega), show t + w.length - T = (t - T) + w.length by omega,
    Nat.add_mod_right]

/-- `0 1⁷` repeated is excluded (strip width 5, 4 warm-up periods). Column 1 itself is
(numerically) not eventually periodic for this driver: this needs the weakened form of Jen. -/

def wordOf (n bits : Nat) : List Bool := (List.range n).map fun i => bits.testBit (n - 1 - i)

/-- C4 word 00000011 (length 8), strip width 12, 6 warm-up periods. -/
theorem c4_00000011 :
    ¬ ∃ T, ∀ t, T ≤ t → cell t 0 = (wordOf 8 3).getD ((t - T) % (wordOf 8 3).length) false :=
  not_eventually_word_strip (wordOf 8 3) 12 6 (by decide) (by decide) (by decide +kernel)

end Rule30JenWindow
end Ruliology.CellularAutomata

open Ruliology.CellularAutomata.Rule30JenWindow
#print axioms c4_00000011
#eval wordOf 8 3
