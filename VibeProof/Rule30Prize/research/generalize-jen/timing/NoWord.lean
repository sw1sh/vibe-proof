import Ruliology.CellularAutomata.Rule30Prize

/-!
# Rule 30: a windowed, weakened form of Jen's theorem, and the long-runs-of-ones exclusion

Jen's adjacent-column argument (`Rule30Jen.not_adjacent`) needs two adjacent columns that are both
eventually periodic. Here the hypothesis on the right-hand column is weakened as far as the
left-permutive reconstruction allows.

* `determine`: the cells of columns `i - 1, i - 2, …` are determined by column `i` and by
  `orCol i = column i || column (i + 1)`. Column `i + 1` only matters where column `i` is white.
* `window_jen`: **no periodicity needed**. Two different times `t₁ < t₂` never carry the same
  pair of words (column `0` on `[t, t + t₂]`, `orCol 0` on `[t, t + t₂)`): the reconstructed
  cell at column `-t₂` would be white at time `t₁` (left of the edge) and black at time `t₂` (on it).
* `periodic_window`: if the center column has period `P` from `T`, then every interval `[n, 2n)` with
  `n ≥ T + P` contains a time `s` with `center s = false` and `cell s 1 ≠ cell (s - P) 1`.
* `or_not_eventuallyPeriodic`: if the center column is eventually periodic, then
  `center || column 1` is not. So column 1 cannot be eventually periodic even if we only look at the
  times where the center is white.
* `nine_ones`: nine consecutive black cells in any column force the next two cells to the right
  (one step later) to be white, black. Checked over all `2 ^ 11` states of the light cone.
* `not_eventuallyPeriodic_of_long_one_runs`: if from some time on every maximal run of black cells in
  the center column that is followed by a white cell has length at least `9`, the center column is
  not eventually periodic. Column 1 need not be eventually periodic here (numerically it is not), so
  this uses the weakened form.
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

/-! ### Long runs of black cells in the center column -/

/-- Inside a white run of the center column that starts right after nine black cells, column 1 is
white at the first white cell and black at the later ones. -/
theorem col1_in_white_run {T : Nat}
    (hruns : ∀ u, T ≤ u → cell (u + 9) 0 = false → cell (u + 8) 0 = true →
      ∀ s, s < 9 → cell (u + s) 0 = true) :
    ∀ k u, T ≤ u → cell (u + 8) 0 = true → (∀ i, i ≤ k → cell (u + 9 + i) 0 = false) →
      cell (u + 9 + k) 1 = decide (k ≠ 0) ∧ (k = 0 → cell (u + 9) 2 = true) := by
  intro k
  induction k with
  | zero =>
    intro u hu h8 hz
    have h9 := nine_ones (j := 0) (hruns u hu (hz 0 (by omega)) h8)
    refine ⟨?_, fun _ => ?_⟩
    · simpa using h9.1
    · simpa using h9.2
  | succ k ih =>
    intro u hu h8 hz
    refine ⟨?_, fun h => absurd h (by omega)⟩
    have hk0 : cell (u + 9 + k) 0 = false := hz k (by omega)
    have hstep : cell (u + 9 + (k + 1)) 1 =
        rule (cell (u + 9 + k) 0) (cell (u + 9 + k) 1) (cell (u + 9 + k) 2) := by
      show rule (cell (u + 9 + k) (1 - 1)) (cell (u + 9 + k) 1) (cell (u + 9 + k) (1 + 1)) = _
      rfl
    have ih' := ih u hu h8 (fun i hi => hz i (by omega))
    rw [hstep, hk0]
    cases k with
    | zero =>
      have e1 : cell (u + 9 + 0) 1 = false := ih'.1
      have e2 : cell (u + 9) 2 = true := ih'.2 rfl
      rw [e1, show u + 9 + 0 = u + 9 from rfl, e2]
      rfl
    | succ k =>
      rw [ih'.1]
      rfl

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

/-- **Long black runs exclude periodicity.** Suppose that from time `T` on, every black run of the
center column that is followed by a white cell has length at least `9`. Then the center column is
not eventually periodic. -/
theorem not_eventuallyPeriodic_of_long_one_runs {T : Nat}
    (hruns : ∀ u, T ≤ u → cell (u + 9) 0 = false → cell (u + 8) 0 = true →
      ∀ s, s < 9 → cell (u + s) 0 = true) :
    ¬ EventuallyPeriodic fun t => cell t 0 := by
  intro hc
  obtain ⟨T₀, P, hP, hper⟩ := hc
  have hper' : ∀ t, T₀ ≤ t → cell (t + P) 0 = cell t 0 := hper
  by_cases hw : ∃ t, T₀ ≤ t ∧ ∀ s, s < P → cell (t + s) 0 = false
  · -- a white period window: the center column is eventually white
    obtain ⟨t, ht, hs⟩ := hw
    have hk : ∀ k s, s < P → cell (t + k * P + s) 0 = false := by
      intro k
      induction k with
      | zero => intro s hs'; simpa using hs s hs'
      | succ k ih =>
        intro s hs'
        rw [show t + (k + 1) * P + s = (t + k * P + s) + P by rw [Nat.succ_mul]; omega,
          hper' _ (by omega)]
        exact ih s hs'
    refine Rule30Prize.no_column_eventually_constant 0 ⟨t, false, fun u hu => ?_⟩
    have := hk ((u - t) / P) ((u - t) % P) (Nat.mod_lt _ hP)
    rwa [show t + (u - t) / P * P + (u - t) % P = u by
      have := Nat.div_add_mod (u - t) P; rw [Nat.mul_comm] at this; omega] at this
  · -- every period window after `T₀` contains a black cell
    have hblack : ∀ t, T₀ ≤ t → ∃ s, s < P ∧ cell (t + s) 0 = true := by
      intro t ht
      refine Classical.byContradiction fun hne => hw ⟨t, ht, fun s hs => ?_⟩
      cases h : cell (t + s) 0
      · rfl
      · exact absurd ⟨s, hs, h⟩ hne
    let B := T + T₀ + P + 10
    have hform : ∀ t, B ≤ t → orCol 0 t = (cell t 0 || !cell (t - 1) 0) := by
      intro t ht
      cases h0 : cell t 0
      · rcases trailing (fun u => cell u 0) t h0 P with hall | ⟨k, hk, h1, h2⟩
        · obtain ⟨s, hs, hb⟩ := hblack (t - P) (by omega)
          have := hall (P - s) (by omega)
          rw [show t - (P - s) = t - P + s by omega, hb] at this
          exact absurd this (by decide)
        · have hrun := col1_in_white_run hruns k (t - (k + 1) - 8) (by omega)
            (by rw [show t - (k + 1) - 8 + 8 = t - (k + 1) by omega]; exact h1)
            (fun i hi => by
              rw [show t - (k + 1) - 8 + 9 + i = t - (k - i) by omega]; exact h2 (k - i) (by omega))
          rw [show t - (k + 1) - 8 + 9 + k = t by omega] at hrun
          unfold orCol
          rw [h0]
          simp only [Int.zero_add, Bool.false_or]
          rw [hrun.1]
          cases k with
          | zero =>
            have : cell (t - 1) 0 = true := by simpa using h1
            rw [this]; rfl
          | succ k =>
            have : cell (t - 1) 0 = false := by simpa using h2 1 (by omega)
            rw [this]; rfl
      · unfold orCol; rw [h0]; rfl
    refine or_not_eventuallyPeriodic ⟨T₀, P, hP, hper⟩ ⟨B, P, hP, fun t ht => ?_⟩
    show orCol 0 (t + P) = orCol 0 t
    rw [hform t (by omega), hform (t + P) (by omega), hper' t (by omega),
      show t + P - 1 = (t - 1) + P by omega, hper' (t - 1) (by omega)]

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

end Rule30JenWindow
end Ruliology.CellularAutomata
