/-!
# Rule 30: no two columns are both eventually periodic (Jen 1986)

Wolfram, *Announcing the Rule 30 Prizes* (2019): "Erica Jen showed in 1986 that no two columns
can both become periodic." The pattern is the classic evolution of rule 30 from a single black
cell.
<https://writings.stephenwolfram.com/2019/10/announcing-the-rule-30-prizes/>
E. Jen, *Global properties of cellular automata*, J. Stat. Phys. 43 (1986) 219–242.

* `jen`: two different columns of the pattern are never both eventually periodic.
* `periodic_column_unique`: at most one column is eventually periodic. Whether the center column
  is aperiodic, the Rule 30 Prize's Problem 1, is open.

**Proof.**
- Rule 30 is `l xor (c || r)`, so `cell t (i - 1) = cell (t + 1) i xor (cell t i || cell t (i + 1))`
  (`cell_left`). If two adjacent columns are eventually periodic (same start, same period), every
  column to their left is too (`periodic_left_all`).
- That is impossible: the left edge of the pattern moves left one cell per step. Far to the left,
  a column is white until the edge reaches it and black at that moment, which contradicts
  periodicity (`no_left_periodic`).
- For columns `j < k` that are not adjacent: the strip strictly between them evolves
  deterministically from its own state and the two boundary columns (`strip_agree`). With
  eventually periodic boundaries, pigeonhole over the `2 ^ (k - j - 1)` strip states makes the
  strip eventually periodic (`between_periodic`). So column `j + 1` is eventually periodic, and
  the adjacent case applies.
-/

namespace Ruliology.CellularAutomata
namespace Rule30Jen

/-- Rule 30: `left xor (center || right)`. -/
def rule (a b c : Bool) : Bool := xor a (b || c)

/-- Rule 30 from a single black cell at position `0`: `cell t p` is the color (`true` = black)
at position `p` after `t` steps. -/
def cell : Nat → Int → Bool
  | 0, p => decide (p = 0)
  | t + 1, p => rule (cell t (p - 1)) (cell t p) (cell t (p + 1))

/-- A sequence of colors is eventually periodic. -/
def EventuallyPeriodic (f : Nat → Bool) : Prop := ∃ T P : Nat, 0 < P ∧ ∀ t, T ≤ t → f (t + P) = f t

/-! ### The left edge -/

theorem cell_eq_false_of_lt : ∀ (t : Nat) (p : Int), p < -(t : Int) → cell t p = false
  | 0, p, h => by simp [cell]; omega
  | t + 1, p, h => by
    show rule (cell t (p - 1)) (cell t p) (cell t (p + 1)) = false
    rw [cell_eq_false_of_lt t (p - 1) (by omega), cell_eq_false_of_lt t p (by omega),
      cell_eq_false_of_lt t (p + 1) (by omega)]
    rfl

/-- The leftmost black cell is at `-t`. -/
theorem cell_left_edge : ∀ t : Nat, cell t (-(t : Int)) = true
  | 0 => rfl
  | t + 1 => by
    show rule (cell t (-((t + 1 : Nat) : Int) - 1)) (cell t (-((t + 1 : Nat) : Int)))
      (cell t (-((t + 1 : Nat) : Int) + 1)) = true
    rw [cell_eq_false_of_lt t _ (by omega), cell_eq_false_of_lt t _ (by omega),
      show -((t + 1 : Nat) : Int) + 1 = -(t : Int) by omega, cell_left_edge t]
    rfl

/-! ### Reconstruction to the left -/

theorem cell_left (t : Nat) (i : Int) :
    cell t (i - 1) = xor (cell (t + 1) i) (cell t i || cell t (i + 1)) := by
  show cell t (i - 1) = xor (rule (cell t (i - 1)) (cell t i) (cell t (i + 1))) (cell t i || cell t (i + 1))
  cases cell t (i - 1) <;> cases cell t i <;> cases cell t (i + 1) <;> rfl

theorem periodic_left {T P : Nat} {i : Int}
    (h0 : ∀ t, T ≤ t → cell (t + P) i = cell t i)
    (h1 : ∀ t, T ≤ t → cell (t + P) (i + 1) = cell t (i + 1)) :
    ∀ t, T ≤ t → cell (t + P) (i - 1) = cell t (i - 1) := by
  intro t ht
  rw [cell_left, cell_left t, show t + P + 1 = (t + 1) + P by omega, h0 (t + 1) (by omega),
    h0 t ht, h1 t ht]

/-- If two adjacent columns are periodic from `T` with period `P`, so is every column to their
left. -/
theorem periodic_left_all {T P : Nat} {i : Int}
    (h0 : ∀ t, T ≤ t → cell (t + P) i = cell t i)
    (h1 : ∀ t, T ≤ t → cell (t + P) (i + 1) = cell t (i + 1)) :
    ∀ m : Nat, (∀ t, T ≤ t → cell (t + P) (i - m) = cell t (i - m)) ∧
      ∀ t, T ≤ t → cell (t + P) (i - m + 1) = cell t (i - m + 1) := by
  intro m
  induction m with
  | zero => simpa using ⟨h0, h1⟩
  | succ m ih =>
    refine ⟨?_, ?_⟩
    · have := periodic_left ih.1 ih.2
      rwa [show i - (m : Int) - 1 = i - ((m + 1 : Nat) : Int) by omega] at this
    · rw [show i - ((m + 1 : Nat) : Int) + 1 = i - (m : Int) by omega]
      exact ih.1

/-- No column far enough to the left is periodic: the edge reaches it once. -/
theorem no_left_periodic {T P : Nat} (hP : 0 < P) {i : Int}
    (h : ∀ m : Nat, ∀ t, T ≤ t → cell (t + P) (i - m) = cell t (i - m)) : False := by
  -- a column `q ≤ i` left of `-(T + P)`
  let q : Int := min i (-((T + P : Nat) : Int) - 1)
  have hq : q ≤ i := Int.min_le_left _ _
  have hq' : q ≤ -((T + P : Nat) : Int) - 1 := Int.min_le_right _ _
  obtain ⟨t₁, ht₁⟩ : ∃ t₁ : Nat, (t₁ : Int) = -q := ⟨(-q).toNat, by omega⟩
  have hper := h (i - q).toNat (t₁ - P) (by omega)
  rw [show i - (((i - q).toNat : Nat) : Int) = q by omega, show t₁ - P + P = t₁ by omega] at hper
  have hedge : cell t₁ q = true := by
    have := cell_left_edge t₁
    rwa [show -(t₁ : Int) = q by omega] at this
  have hwhite : cell (t₁ - P) q = false := cell_eq_false_of_lt _ _ (by omega)
  rw [hedge, hwhite] at hper
  exact absurd hper (by decide)

/-! ### Periods -/

theorem periodic_mul {f : Nat → Bool} {T P : Nat} (h : ∀ t, T ≤ t → f (t + P) = f t) :
    ∀ n t, T ≤ t → f (t + n * P) = f t
  | 0, t, _ => by simp
  | n + 1, t, ht => by
    rw [show t + (n + 1) * P = (t + n * P) + P by rw [Nat.succ_mul]; omega,
      h (t + n * P) (by omega), periodic_mul h n t ht]

/-- Two eventually periodic sequences share a start and a period. -/
theorem common_period {f g : Nat → Bool} (hf : EventuallyPeriodic f) (hg : EventuallyPeriodic g) :
    ∃ T P : Nat, 0 < P ∧ (∀ t, T ≤ t → f (t + P) = f t) ∧ ∀ t, T ≤ t → g (t + P) = g t := by
  obtain ⟨T₁, P₁, hP₁, h₁⟩ := hf
  obtain ⟨T₂, P₂, hP₂, h₂⟩ := hg
  refine ⟨max T₁ T₂, P₁ * P₂, Nat.mul_pos hP₁ hP₂, fun t ht => ?_, fun t ht => ?_⟩
  · rw [Nat.mul_comm]; exact periodic_mul h₁ P₂ t (by omega)
  · exact periodic_mul h₂ P₁ t (by omega)

/-! ### The strip between two columns -/

/-- The cells strictly between columns `j` and `k` at step `t`. -/
def strip (j k : Int) (t : Nat) : List Bool :=
  (List.range (k - j - 1).toNat).map fun (r : Nat) => cell t (j + 1 + (r : Int))

set_option linter.unusedSimpArgs false in
/-- The strip evolves from its own state and the two boundary columns. -/
theorem strip_agree {j k : Int} (hjk : j < k) {t₁ t₂ : Nat} (hs : strip j k t₁ = strip j k t₂)
    (hb : ∀ r, cell (t₁ + r) j = cell (t₂ + r) j ∧ cell (t₁ + r) k = cell (t₂ + r) k) :
    ∀ r, ∀ i, j ≤ i → i ≤ k → cell (t₁ + r) i = cell (t₂ + r) i := by
  intro r
  induction r with
  | zero =>
    intro i hi1 hi2
    by_cases e1 : i = j
    · subst e1; exact (hb 0).1
    by_cases e2 : i = k
    · subst e2; exact (hb 0).2
    have := congrArg (fun l => l.getD (i - j - 1).toNat false) hs
    simp only [strip, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_range (show (i - j - 1).toNat < (k - j - 1).toNat by omega),
      Option.map_some, Option.getD_some] at this
    rwa [show j + 1 + (((i - j - 1).toNat : Nat) : Int) = i by omega] at this
  | succ r ih =>
    intro i hi1 hi2
    by_cases e1 : i = j
    · subst e1; exact (hb (r + 1)).1
    by_cases e2 : i = k
    · subst e2; exact (hb (r + 1)).2
    show rule (cell (t₁ + r) (i - 1)) (cell (t₁ + r) i) (cell (t₁ + r) (i + 1)) =
      rule (cell (t₂ + r) (i - 1)) (cell (t₂ + r) i) (cell (t₂ + r) (i + 1))
    rw [ih (i - 1) (by omega) (by omega), ih i (by omega) (by omega), ih (i + 1) (by omega) (by omega)]

/-- All Boolean lists of length `n`. -/
def allLists : Nat → List (List Bool)
  | 0 => [[]]
  | n + 1 => (allLists n).map (false :: ·) ++ (allLists n).map (true :: ·)

theorem mem_allLists : ∀ (l : List Bool), l ∈ allLists l.length
  | [] => by simp [allLists]
  | b :: l => by
    cases b <;> simp [allLists, mem_allLists l]

theorem length_allLists : ∀ n, (allLists n).length = 2 ^ n
  | 0 => rfl
  | n + 1 => by simp [allLists, length_allLists n, Nat.pow_succ]; omega

theorem length_le_of_subset {α : Type} [DecidableEq α] :
    ∀ {l₁ l₂ : List α}, l₁.Nodup → (∀ x ∈ l₁, x ∈ l₂) → l₁.length ≤ l₂.length
  | [], _, _, _ => Nat.zero_le _
  | x :: l₁, l₂, hn, hs => by
    rw [List.nodup_cons] at hn
    have hx : x ∈ l₂ := hs x (by simp)
    have := length_le_of_subset (l₂ := l₂.erase x) hn.2 fun y hy =>
      (List.mem_erase_of_ne (fun (e : y = x) => hn.1 (by rw [← e]; exact hy))).2 (hs y (by simp [hy]))
    rw [List.length_erase_of_mem hx] at this
    simp only [List.length_cons]
    have : 0 < l₂.length := List.length_pos_of_mem hx
    omega

theorem nodup_map_of_inj {α β : Type} (f : α → β) : ∀ {l : List α}, l.Nodup →
    (∀ a ∈ l, ∀ b ∈ l, f a = f b → a = b) → (l.map f).Nodup
  | [], _, _ => List.nodup_nil
  | a :: l, hl, hinj => by
    rw [List.nodup_cons] at hl
    rw [List.map_cons, List.nodup_cons]
    refine ⟨?_, nodup_map_of_inj f hl.2 fun x hx y hy => hinj x (by simp [hx]) y (by simp [hy])⟩
    intro hm
    obtain ⟨b, hb, hfb⟩ := List.mem_map.1 hm
    exact hl.1 (hinj a (by simp) b (by simp [hb]) hfb.symm ▸ hb)

/-- Pigeonhole: among `2 ^ w + 1` lists of length `w`, two are equal. -/
theorem pigeonhole (w : Nat) (a : Nat → List Bool) (ha : ∀ m, (a m).length = w) :
    ∃ m n, m < n ∧ n ≤ 2 ^ w ∧ a m = a n := by
  refine Classical.byContradiction fun hne => ?_
  have hinj : ∀ m ∈ List.range (2 ^ w + 1), ∀ n ∈ List.range (2 ^ w + 1), a m = a n → m = n := by
    intro m hm n hn e
    simp only [List.mem_range] at hm hn
    rcases Nat.lt_trichotomy m n with h | h | h
    · exact absurd ⟨m, n, h, by omega, e⟩ hne
    · exact h
    · exact absurd ⟨n, m, h, by omega, e.symm⟩ hne
  have hnd := nodup_map_of_inj a List.nodup_range hinj
  have := length_le_of_subset hnd fun x hx => by
    obtain ⟨m, -, rfl⟩ := List.mem_map.1 hx
    have := mem_allLists (a m)
    rwa [ha m] at this
  simp only [List.length_map, List.length_range, length_allLists] at this
  omega

/-- **Between two eventually periodic columns, the next column is eventually periodic.** -/
theorem between_periodic {j k : Int} (hjk : j + 1 < k)
    (hj : EventuallyPeriodic fun t => cell t j) (hk : EventuallyPeriodic fun t => cell t k) :
    EventuallyPeriodic fun t => cell t (j + 1) := by
  obtain ⟨T, P, hP, hpj, hpk⟩ := common_period hj hk
  obtain ⟨m, n, hmn, -, he⟩ := pigeonhole (k - j - 1).toNat (fun m => strip j k (T + m * P))
    (fun m => by simp only [strip, List.length_map, List.length_range])
  refine ⟨T + m * P, (n - m) * P, Nat.mul_pos (by omega) hP, fun t ht => ?_⟩
  have key := strip_agree (by omega) he (fun r => ⟨?_, ?_⟩) (t - (T + m * P)) (j + 1) (by omega) (by omega)
  · rw [show T + m * P + (t - (T + m * P)) = t by omega,
      show T + n * P + (t - (T + m * P)) = t + (n - m) * P by
        rw [Nat.sub_mul]; have : m * P ≤ n * P := Nat.mul_le_mul_right _ (by omega); omega] at key
    exact key.symm
  · rw [show T + n * P + r = (T + m * P + r) + (n - m) * P by
      rw [Nat.sub_mul]; have : m * P ≤ n * P := Nat.mul_le_mul_right _ (by omega); omega]
    exact (periodic_mul (f := fun t => cell t j) hpj (n - m) _ (by omega)).symm
  · rw [show T + n * P + r = (T + m * P + r) + (n - m) * P by
      rw [Nat.sub_mul]; have : m * P ≤ n * P := Nat.mul_le_mul_right _ (by omega); omega]
    exact (periodic_mul (f := fun t => cell t k) hpk (n - m) _ (by omega)).symm

/-! ### Jen's theorem -/

/-- Two adjacent columns are never both eventually periodic. -/
theorem not_adjacent (i : Int) (h0 : EventuallyPeriodic fun t => cell t i)
    (h1 : EventuallyPeriodic fun t => cell t (i + 1)) : False := by
  obtain ⟨T, P, hP, hp0, hp1⟩ := common_period h0 h1
  exact no_left_periodic hP fun m => (periodic_left_all hp0 hp1 m).1

/-- **Jen's theorem.** No two different columns of rule 30 from a single black cell are both
eventually periodic. -/
theorem jen (j k : Int) (hjk : j ≠ k) :
    ¬ (EventuallyPeriodic (fun t => cell t j) ∧ EventuallyPeriodic (fun t => cell t k)) := by
  have lt_case : ∀ a b : Int, a < b → (EventuallyPeriodic fun t => cell t a) →
      (EventuallyPeriodic fun t => cell t b) → False := by
    intro a b hab ha hb
    by_cases hadj : b = a + 1
    · subst hadj; exact not_adjacent a ha hb
    · exact not_adjacent a ha (between_periodic (by omega) ha hb)
  rintro ⟨hj, hk⟩
  rcases Int.lt_or_gt_of_ne hjk with h | h
  · exact lt_case j k h hj hk
  · exact lt_case k j h hk hj

/-- **At most one column is eventually periodic.** -/
theorem periodic_column_unique (j k : Int) (hj : EventuallyPeriodic fun t => cell t j)
    (hk : EventuallyPeriodic fun t => cell t k) : j = k :=
  Classical.byContradiction fun h => jen j k h ⟨hj, hk⟩

end Rule30Jen
end Ruliology.CellularAutomata


/-!
# The Rule 30 Prize problems: statements, and the constant case of Problem 1

Wolfram, *Announcing the Rule 30 Prizes* (2019):
<https://writings.stephenwolfram.com/2019/10/announcing-the-rule-30-prizes/>

    Problem 1: Does the center column always remain non-periodic?
    Problem 2: Does each color of cell occur on average equally often in the center column?
    Problem 3: Does computing the nth cell of the center column require at least O(n)
               computational effort?

All three are open.

* `Problem1`, `Problem2`: the first two problems as statements about `cell` from `Rule30Jen`.
  They match `Rule30.centerColumn_not_eventually_periodic` and
  `Rule30.centerColumn_frequency_half` in google-deepmind/formal-conjectures
  (`FormalConjectures/Other/Rule30.lean`), whose `state t i` is `cell t i`. Problem 3 needs a
  model of computation and is not stated here.
* `no_column_eventually_constant`: **no column is eventually constant**. This settles the period-1
  case of Problem 1, for every column and every transient. If a column is eventually black, the
  column to its left is eventually white. If it is eventually white, the column to its right can
  only turn from white to black, so it is eventually constant. Either way two adjacent columns are
  eventually periodic, which Jen's theorem (`Rule30Jen.not_adjacent`) rules out.
* `center_not_eventually_constant`: the center column in particular.
-/

namespace Ruliology.CellularAutomata
namespace Rule30Prize

open Rule30Jen

/-- The center column: the color of the cell at position `0` at time `t`. -/
def center (t : Nat) : Bool := cell t 0

/-- **Problem 1**: the center column is not eventually periodic. -/
def Problem1 : Prop := ¬ EventuallyPeriodic center

/-- The number of black cells among `center 0, …, center (n - 1)`. -/
def blackCount (n : Nat) : Nat := ((List.range n).filter center).length

/-- **Problem 2**: black cells have density `1/2` in the center column, stated with integers:
for every `k > 0`, eventually `k · |2 · blackCount n − n| ≤ n`. -/
def Problem2 : Prop :=
  ∀ k : Nat, 0 < k → ∃ N, ∀ n, N ≤ n → k * (2 * (blackCount n : Int) - n).natAbs ≤ n

/-- An eventually constant sequence is eventually periodic. -/
theorem eventuallyPeriodic_of_const {f : Nat → Bool} {T : Nat} {b : Bool}
    (h : ∀ t, T ≤ t → f t = b) : EventuallyPeriodic f :=
  ⟨T, 1, Nat.one_pos, fun t ht => (h (t + 1) (by omega)).trans (h t ht).symm⟩

/-- A sequence that can only turn from white to black is eventually constant. -/
theorem eventually_const_of_mono {f : Nat → Bool} {T : Nat}
    (h : ∀ t, T ≤ t → f t = true → f (t + 1) = true) : ∃ T' b, ∀ t, T' ≤ t → f t = b := by
  by_cases hx : ∃ t, T ≤ t ∧ f t = true
  · obtain ⟨t₀, ht₀, hf⟩ := hx
    have hk : ∀ k, f (t₀ + k) = true := by
      intro k
      induction k with
      | zero => exact hf
      | succ k ih => exact h (t₀ + k) (by omega) ih
    refine ⟨t₀, true, fun t ht => ?_⟩
    have := hk (t - t₀)
    rwa [show t₀ + (t - t₀) = t by omega] at this
  · refine ⟨T, false, fun t ht => ?_⟩
    cases hft : f t
    · rfl
    · exact absurd ⟨t, ht, hft⟩ hx

/-- **No column of rule 30 is eventually constant.** -/
theorem no_column_eventually_constant (i : Int) : ¬ ∃ T b, ∀ t, T ≤ t → cell t i = b := by
  rintro ⟨T, b, h⟩
  cases b
  · -- column `i` is eventually white: column `i + 1` can only turn black
    have hmono : ∀ t, T ≤ t → cell t (i + 1) = true → cell (t + 1) (i + 1) = true := by
      intro t ht h1
      show rule (cell t (i + 1 - 1)) (cell t (i + 1)) (cell t (i + 1 + 1)) = true
      rw [show i + 1 - 1 = i by omega, h t ht, h1]
      rfl
    obtain ⟨T', b', h'⟩ := eventually_const_of_mono hmono
    exact not_adjacent i (eventuallyPeriodic_of_const h) (eventuallyPeriodic_of_const h')
  · -- column `i` is eventually black: column `i - 1` is eventually white
    have hleft : ∀ t, T ≤ t → cell t (i - 1) = false := by
      intro t ht
      have e := h (t + 1) (by omega)
      have hc : cell (t + 1) i = rule (cell t (i - 1)) (cell t i) (cell t (i + 1)) := rfl
      rw [hc, h t ht] at e
      revert e
      cases cell t (i - 1) <;> simp [rule]
    refine not_adjacent (i - 1) (eventuallyPeriodic_of_const hleft) ?_
    rw [show i - 1 + 1 = i by omega]
    exact eventuallyPeriodic_of_const h

/-- **The center column is not eventually constant**: Problem 1 for period `1`. -/
theorem center_not_eventually_constant : ¬ ∃ T b, ∀ t, T ≤ t → center t = b :=
  no_column_eventually_constant 0

/-- The same, in the shape of Problem 1: no transient `N` after which the center column has
period `1`. -/
theorem center_not_eventually_period_one : ¬ ∃ N, ∀ t, N ≤ t → center (t + 1) = center t := by
  rintro ⟨N, h⟩
  have hk : ∀ k, center (N + k) = center N := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => rw [← Nat.add_assoc, h (N + k) (by omega), ih]
  refine center_not_eventually_constant ⟨N, center N, fun t ht => ?_⟩
  have := hk (t - N)
  rwa [show N + (t - N) = t by omega] at this

end Rule30Prize
end Ruliology.CellularAutomata


/-!
# Rule 30: the center column is not eventually periodic with a period word whose 1-runs are long

Scratch development (smallperiods agent, 2026-10-15).

* `absorb`: if the center column is black for 9 consecutive steps, then at the end of those
  steps column 1 is white and column 2 is black. (Finite check over the 2^11 possible contents of
  columns 1..11.)
* `effective_boundary`: `cell t (-1) || c t = cell t (-1) || (c t && c (t+1))` for every `t`,
  i.e. the left half only ever "sees" the center column through `c t && c (t + 1)`.
* `no_period_long_ones`: if the center column is eventually periodic and, from some point on,
  every maximal run of black center cells has length at least 9, then column 1 is forced at every
  white center cell, so column `-1` is eventually periodic too — contradicting Jen's theorem
  (`not_adjacent (-1)`). So no period word whose cyclic 1-runs all have length ≥ 9 can occur,
  whatever the transient.
-/

namespace R30SmallPeriods
open Ruliology.CellularAutomata.Rule30Jen
open Ruliology.CellularAutomata.Rule30Prize

/-! ### Evolving a finite window -/

/-- One rule-30 step on a window: `c` is the cell just left of the window, `l` the window (left to
right). The result holds the next values of every window cell except the last one. -/
def stepW (c : Bool) : List Bool → List Bool
  | [] => []
  | [_] => []
  | x :: y :: rest => rule c x y :: stepW x (y :: rest)

/-- The `n` cells at positions `a, a+1, …, a+n-1` at step `t`. -/
def win (t : Nat) (a : Int) : Nat → List Bool
  | 0 => []
  | n + 1 => cell t a :: win t (a + 1) n

theorem win_length (t : Nat) : ∀ (a : Int) (n : Nat), (win t a n).length = n
  | _, 0 => rfl
  | a, n + 1 => by simp [win, win_length t (a + 1) n]

theorem stepW_win (t : Nat) : ∀ (n : Nat) (a : Int),
    stepW (cell t (a - 1)) (win t a (n + 1)) = win (t + 1) a n
  | 0, a => by simp [win, stepW]
  | n + 1, a => by
    have ih := stepW_win t n (a + 1)
    rw [show a + 1 - 1 = a by omega] at ih
    show rule (cell t (a - 1)) (cell t a) (cell t (a + 1)) :: stepW (cell t a) (win t (a + 1) (n + 1))
      = cell (t + 1) a :: win (t + 1) (a + 1) n
    rw [ih]
    rfl

/-- `k` steps of the right half with a black center column. -/
def runTrue : Nat → List Bool → List Bool
  | 0, l => l
  | k + 1, l => runTrue k (stepW true l)

theorem runTrue_win : ∀ (k t n : Nat), (∀ i, i < k → cell (t + i) 0 = true) →
    runTrue k (win t 1 (n + k)) = win (t + k) 1 n
  | 0, t, n, _ => rfl
  | k + 1, t, n, h => by
    have h0 : cell t 0 = true := by simpa using h 0 (by omega)
    have hs : stepW true (win t 1 ((n + k) + 1)) = win (t + 1) 1 (n + k) := by
      have := stepW_win t (n + k) 1
      rw [show (1 : Int) - 1 = 0 by rfl, h0] at this
      exact this
    show runTrue k (stepW true (win t 1 ((n + k) + 1))) = win (t + (k + 1)) 1 n
    rw [hs, runTrue_win k (t + 1) n (fun i hi => by
      rw [show t + 1 + i = t + (i + 1) by omega]; exact h (i + 1) (by omega))]
    rw [show t + 1 + k = t + (k + 1) by omega]

/-- The finite check: 9 black center steps send every window `x₁ … x₁₁` to `(white, black)`. -/
theorem absorb_check : (allLists 11).all (fun l => runTrue 9 l == [false, true]) = true := by
  decide +kernel

/-- **Absorption.** Nine consecutive black center cells force column 1 white and column 2 black. -/
theorem absorb (t : Nat) (h : ∀ i, i < 9 → cell (t + i) 0 = true) :
    cell (t + 9) 1 = false ∧ cell (t + 9) 2 = true := by
  have hw := runTrue_win 9 t 2 h
  have hmem : win t 1 (2 + 9) ∈ allLists 11 := by
    have := mem_allLists (win t 1 (2 + 9))
    rwa [win_length] at this
  have hc := List.all_eq_true.1 absorb_check _ hmem
  rw [hw] at hc
  have : win (t + 9) 1 2 = [false, true] := by simpa using hc
  simp only [win] at this
  injection this with h1 h2
  injection h2 with h2 _
  exact ⟨h1, by simpa using h2⟩

/-- Once column 1 is white and column 2 black, a black center keeps them so. -/
theorem absorb_stay (t : Nat) (h1 : cell t 1 = false) (h2 : cell t 2 = true)
    (hc : cell t 0 = true) : cell (t + 1) 1 = false ∧ cell (t + 1) 2 = true := by
  constructor
  · show rule (cell t (1 - 1)) (cell t 1) (cell t (1 + 1)) = false
    rw [show (1 : Int) - 1 = 0 by rfl, hc, h1, show (1 : Int) + 1 = 2 by rfl, h2]; rfl
  · show rule (cell t (2 - 1)) (cell t 2) (cell t (2 + 1)) = true
    rw [show (2 : Int) - 1 = 1 by rfl, h1, h2]; rfl

/-! ### The effective boundary of the left half -/

/-- The left half sees the center column only through `c t && c (t + 1)`. -/
theorem effective_boundary (t : Nat) :
    (cell t (-1) || center t) = (cell t (-1) || (center t && center (t + 1))) := by
  have hl := cell_left t 0
  rw [show (0 : Int) - 1 = -1 by rfl] at hl
  unfold center
  rw [hl]
  cases cell (t + 1) 0 <;> cases cell t 0 <;> cases cell t (0 + 1) <;> rfl

/-- If the center is black and white next, column `-1` is black. -/
theorem left_of_black (t : Nat) (h : center t = true) :
    cell t (-1) = !center (t + 1) := by
  have hl := cell_left t 0
  rw [show (0 : Int) - 1 = -1 by rfl] at hl
  unfold center at h ⊢
  rw [hl, h]
  cases cell (t + 1) 0 <;> rfl

/-! ### Inside a white run of the center column -/

/-- During a white run of the center, once column 1 or column 2 is black, column 1 stays black. -/
theorem white_run (t : Nat) (h : (cell t 1 || cell t 2) = true) (hc : center t = false) :
    cell (t + 1) 1 = true := by
  show rule (cell t (1 - 1)) (cell t 1) (cell t (1 + 1)) = true
  unfold center at hc
  rw [show (1 : Int) - 1 = 0 by rfl, hc, show (1 : Int) + 1 = 2 by rfl]
  revert h; cases cell t 1 <;> cases cell t 2 <;> simp [rule]

/-! ### The main theorem -/

/-- Walk back from `t` to the first white cell of its white run (stopping at time `lo`). -/
def runStart (lo : Nat) : Nat → Nat
  | 0 => 0
  | t + 1 => if lo < t + 1 ∧ center t = false then runStart lo t else t + 1

theorem runStart_spec (lo : Nat) : ∀ t, lo ≤ t →
    lo ≤ runStart lo t ∧ runStart lo t ≤ t ∧
    (∀ j, runStart lo t ≤ j → j < t → center j = false) ∧
    (lo < runStart lo t → center (runStart lo t - 1) = true)
  | 0, h => by
    have : lo = 0 := by omega
    subst this
    refine ⟨Nat.le_refl _, by simp [runStart], fun j h1 h2 => by omega, fun h => by simp [runStart] at h⟩
  | t + 1, h => by
    by_cases hc : lo < t + 1 ∧ center t = false
    · have e : runStart lo (t + 1) = runStart lo t := by simp [runStart, hc]
      obtain ⟨a, b, c, d⟩ := runStart_spec lo t (by omega)
      rw [e]
      refine ⟨a, by omega, fun j h1 h2 => ?_, d⟩
      by_cases hj : j = t
      · subst hj; exact hc.2
      · exact c j h1 (by omega)
    · have e : runStart lo (t + 1) = t + 1 := by simp [runStart, hc]
      rw [e]
      refine ⟨h, Nat.le_refl _, fun j h1 h2 => by omega, fun h' => ?_⟩
      simp only [Nat.add_sub_cancel]
      cases hct : center t
      · exact absurd ⟨h', hct⟩ hc
      · rfl

/-- **No eventual period with long black runs.** If the center column has period `P` from `T` on,
and from `T + 9` on every white cell that follows a black cell is preceded by at least 9 black
cells, we reach a contradiction: either the center is eventually white (no column is eventually
constant), or column `-1` is eventually periodic alongside column `0` (Jen). -/
theorem no_period_long_ones (T P : Nat) (hP : 0 < P)
    (hper : ∀ t, T ≤ t → center (t + P) = center t)
    (hruns : ∀ t, T + 9 ≤ t → center t = false → center (t - 1) = true →
      ∀ i, i < 9 → center (t - 1 - i) = true) : False := by
  -- periodic shifts
  have hperk : ∀ k t, T ≤ t → center (t + k * P) = center t := by
    intro k; induction k with
    | zero => intro t _; simp
    | succ k ih => intro t ht; rw [show t + (k + 1) * P = (t + k * P) + P by
        rw [Nat.succ_mul]; omega, hper _ (by omega), ih t ht]
  -- Case: the center is eventually constant
  by_cases hone : ∃ u, T ≤ u ∧ u < T + P ∧ center u = true
  case neg =>
    apply center_not_eventually_constant
    refine ⟨T, false, fun t ht => ?_⟩
    have hq : t = (T + (t - T) % P) + ((t - T) / P) * P := by
      have := Nat.mod_add_div (t - T) P; rw [Nat.mul_comm] at this; omega
    rw [hq, hperk _ _ (by omega)]
    cases hc : center (T + (t - T) % P)
    · rfl
    · exact absurd ⟨_, by omega, by have := Nat.mod_lt (t - T) hP; omega, hc⟩ hone
  obtain ⟨u, hu1, hu2, hu⟩ := hone
  -- every window of length P after T contains a black cell
  have hwin : ∀ s, T ≤ s → ∃ v, s ≤ v ∧ v < s + P ∧ center v = true := by
    intro s hs
    -- v = u + k P for the right k
    have hdm := Nat.div_add_mod (s - u + P - 1) P
    have hml := Nat.mod_lt (s - u + P - 1) hP
    generalize (s - u + P - 1) / P = q at hdm ⊢
    generalize (s - u + P - 1) % P = r at hdm hml
    have hqp : q * P = P * q := Nat.mul_comm _ _
    have hq : q = 0 ∨ P ≤ q * P := by
      rcases Nat.eq_zero_or_pos q with h | h
      · exact Or.inl h
      · exact Or.inr (Nat.le_mul_of_pos_left P h)
    have hq0 : q = 0 → q * P = 0 := fun h => by rw [h]; exact Nat.zero_mul P
    refine ⟨u + q * P, by omega, by omega, ?_⟩
    rw [hperk _ _ hu1]; exact hu
  -- Key: for a white cell t ≥ T + 9 + P, column 1 at t is black iff the center at t-1 is white
  have key : ∀ t, T + 9 + P ≤ t → center t = false → cell t 1 = !center (t - 1) := by
    intro t ht hct
    obtain ⟨s0, s1, s2, s3⟩ := runStart_spec (T + 9) t (by omega)
    -- the run start is strictly after T + 9 (a black cell lies in [t - P, t - 1])
    obtain ⟨v, hv1, hv2, hv⟩ := hwin (t - P) (by omega)
    have hvt : v < t := by
      rcases Nat.lt_or_ge v t with h | h
      · exact h
      · have : v = t := by omega
        subst this; rw [hct] at hv; exact absurd hv (by simp)
    have hstart : T + 9 < runStart (T + 9) t := by
      rcases Nat.lt_or_ge (T + 9) (runStart (T + 9) t) with h | h
      · exact h
      · have := s2 v (by omega) hvt; rw [hv] at this; exact absurd this (by simp)
    have hprev := s3 hstart
    generalize hsdef : runStart (T + 9) t = s at s0 s1 s2 s3 hstart hprev
    -- s is white
    have hs_white : center s = false := by
      rcases Nat.lt_or_ge s t with h | h
      · exact s2 s (Nat.le_refl _) h
      · have : s = t := by omega
        rw [this]; exact hct
    -- absorption at the run start
    have hab := absorb (s - 9) (fun i hi => by
      have := hruns s (by omega) hs_white hprev (8 - i) (by omega)
      unfold center at this
      rw [show s - 1 - (8 - i) = s - 9 + i by omega] at this
      exact this)
    rw [show s - 9 + 9 = s by omega] at hab
    -- walk forward through the white run
    have walk : ∀ j, s < j → j ≤ t → cell j 1 = true := by
      intro j hj1 hj2
      induction j with
      | zero => omega
      | succ j ih =>
        apply white_run j
        · by_cases hjs : j = s
          · subst hjs; rw [hab.1, hab.2]; rfl
          · rw [ih (by omega) (by omega)]; rfl
        · rcases Nat.lt_or_ge j t with h | h
          · exact s2 j (by omega) h
          · omega
    rcases Nat.lt_or_ge s t with h | h
    · rw [walk t h (Nat.le_refl _)]
      have : center (t - 1) = false := s2 (t - 1) (by omega) (by omega)
      rw [this]; rfl
    · have : s = t := by omega
      rw [← this, hab.1, hprev]; rfl
  -- column -1 is eventually periodic
  have hleft : EventuallyPeriodic fun t => cell t (-1) := by
    refine ⟨T + 9 + P + 1, P, hP, fun t ht => ?_⟩
    have form : ∀ t, T + 9 + P + 1 ≤ t →
        cell t (-1) = xor (center (t + 1)) (center t || !center (t - 1)) := by
      intro t ht
      have hl := cell_left t 0
      rw [show (0 : Int) - 1 = -1 by rfl] at hl
      rw [hl]
      show xor (center (t + 1)) (center t || cell t (0 + 1)) = _
      cases hc : center t
      · rw [show (0 : Int) + 1 = 1 by rfl, key t (by omega) hc]
      · rfl
    simp only
    rw [form (t + P) (by omega), form t ht, show t + P + 1 = (t + 1) + P by omega,
      hper (t + 1) (by omega), hper t (by omega), show t + P - 1 = (t - 1) + P by omega,
      hper (t - 1) (by omega)]
  exact not_adjacent (-1) hleft (by
    exact ⟨T, P, hP, fun t ht => by
      show cell (t + P) (-1 + 1) = cell t (-1 + 1)
      rw [show (-1 : Int) + 1 = 0 by rfl]
      exact hper t ht⟩)

end R30SmallPeriods

#print axioms R30SmallPeriods.no_period_long_ones
#print axioms R30SmallPeriods.effective_boundary
#print axioms R30SmallPeriods.absorb

-- ===== verifier additions =====
open Ruliology.CellularAutomata.Rule30Jen Ruliology.CellularAutomata.Rule30Prize in
#eval (List.range 13).map (fun t => if center t then 1 else 0)
#eval [xor true true, xor true false, xor false true, xor false false]
#check @R30SmallPeriods.no_period_long_ones
#print axioms Ruliology.CellularAutomata.Rule30Jen.not_adjacent
#print axioms Ruliology.CellularAutomata.Rule30Prize.center_not_eventually_constant

-- Restate the claim with my own self-contained definitions and derive it.
namespace VerifierC3
def r30 : Nat → Int → Bool
  | 0, p => p == 0
  | t + 1, p => (r30 t (p - 1) != (r30 t p || r30 t (p + 1)))

theorem r30_eq : ∀ t p, r30 t p = Ruliology.CellularAutomata.Rule30Jen.cell t p
  | 0, p => by
    by_cases h : p = 0 <;> simp [r30, Ruliology.CellularAutomata.Rule30Jen.cell, h]
  | t + 1, p => by
    show (r30 t (p - 1) != (r30 t p || r30 t (p + 1))) =
      Ruliology.CellularAutomata.Rule30Jen.rule _ _ _
    rw [r30_eq t (p - 1), r30_eq t p, r30_eq t (p + 1)]
    unfold Ruliology.CellularAutomata.Rule30Jen.rule
    cases Ruliology.CellularAutomata.Rule30Jen.cell t (p - 1) <;>
      cases Ruliology.CellularAutomata.Rule30Jen.cell t p <;>
      cases Ruliology.CellularAutomata.Rule30Jen.cell t (p + 1) <;> rfl

/-- The claim C3, stated independently: for every transient `T` and period `P > 0`, it is not
the case that the center column is `P`-periodic from `T` AND every 1→0 transition at a time
`t ≥ T + 9` is preceded by 9 ones. -/
theorem claimC3 : ∀ T P : Nat, 0 < P →
    ¬ ((∀ t, T ≤ t → r30 (t + P) 0 = r30 t 0) ∧
       (∀ t, T + 9 ≤ t → r30 (t - 1) 0 = true → r30 t 0 = false →
          ∀ k, t - 9 ≤ k → k ≤ t - 1 → r30 k 0 = true)) := by
  intro T P hP ⟨hper, hruns⟩
  refine R30SmallPeriods.no_period_long_ones T P hP (fun t ht => ?_) (fun t ht h0 h1 i hi => ?_)
  · have := hper t ht
    rw [r30_eq, r30_eq] at this
    exact this
  · have := hruns t ht (by rw [r30_eq]; exact h1) (by rw [r30_eq]; exact h0) (t - 1 - i)
      (by omega) (by omega)
    rw [r30_eq] at this
    exact this
end VerifierC3
#print axioms VerifierC3.claimC3
