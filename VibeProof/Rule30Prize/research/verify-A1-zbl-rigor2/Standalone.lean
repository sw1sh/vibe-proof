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
# Period 2 and the zero-boundary left half (Program A, `Q01`)

If the center column of rule 30 alternates from time `T` (black at `T + 2s`, white at `T + 2s + 1`),
then `center t && center (t+1) = false` for `t ≥ T`, so the left half `p ≤ -1` evolves on its own as
rule 30 with a permanently white cell at `p = 0` ("zero-boundary left half", ZBL), and column `-1`
is black at every time `T + 2s`. The left half at time `T` is finitely supported.

`Q01` says: no finitely supported ZBL row keeps column `-1` black at all even times. This file

* defines the ZBL `zrow` (position `k ≥ 1` stands for cell `-k`);
* proves the reduction `Q01 → ¬ (center column eventually 2-periodic)` (`no_period_two_of_Q01`);
* proves the reconstruction ("trace") structure of the ZBL: the boundary column determines the row
  (`zrow_det`), with a pivot at every depth (`zrow_pivot`), and every boundary column occurs
  (`trace_surj`); so the reconstruction map `Phi` (free bits `f_s = zrow L (2s+1) 1` ↦ row) is a
  bijection onto the constrained rows (`Phi_inX`, `Phi_free`) and `Q01 ↔ ∀ f, ¬ FinSupp (Phi f)`
  (`Q01_iff_Phi`);
* proves the identities forced by the constraint at small depth (`L 2 = !f₀`, `L 3 = f₀`, `L 5 = f₀`,
  `L 4 = !f₁`);
* proves that a nonzero finite ZBL row never has an eventually periodic boundary column
  (`trace_not_eventuallyPeriodic`); hence a finite row satisfying the constraint has free bits
  that are not eventually periodic (`free_not_eventuallyPeriodic`);
* proves stripe confinement (`stripe_confined`): a row that agrees with the stripe `1010…` from an
  odd position on keeps agreeing from there on;
* proves stripe absorption (`stripe_absorb`): such a row becomes exactly the stripe after finitely
  many steps. The stripe front moves inward by two cells within `9` steps whatever lies inside it
  (`front_advance`, from a `decide` over the `2 ^ 12` contents of the twelve inner cells), and
  short strips are checked exhaustively. Hence a constrained row with a stripe tail has free bits
  that are eventually all `1` (`stripe_tail_free_eventually_one`). The other phase (black at even
  positions) is absorbed the same way except for cell `1`, which ends up alternating
  (`stripe2_absorb`), so a constrained row with such a tail has free bits eventually all `0`
  (`stripe2_tail_free_eventually_zero`). This is the contrast to `Q01`: stripe backgrounds are
  absorbing, while a white background lets the edge escape.
-/

namespace R30ZBL

open Ruliology.CellularAutomata
open Ruliology.CellularAutomata.Rule30Jen
open Ruliology.CellularAutomata.Rule30Prize

/-- Rule 30 on the half-line `k ≥ 1` with the cell at `k = 0` held white.
`zrow L t k` is the colour at time `t` and position `k` (standing for cell `-k`); `L` is the
initial row, whose value at `0` is ignored. -/
def zrow (L : Nat → Bool) : Nat → Nat → Bool
  | 0, k => if k = 0 then false else L k
  | t + 1, k => if k = 0 then false else xor (zrow L t (k + 1)) (zrow L t k || zrow L t (k - 1))

theorem zrow_zero_pos (L : Nat → Bool) : ∀ t, zrow L t 0 = false
  | 0 => rfl
  | _ + 1 => rfl

theorem zrow_init (L : Nat → Bool) (k : Nat) : zrow L 0 (k + 1) = L (k + 1) := rfl

theorem zrow_succ (L : Nat → Bool) (t k : Nat) :
    zrow L (t + 1) (k + 1) = xor (zrow L t (k + 2)) (zrow L t (k + 1) || zrow L t k) := rfl

/-- Left-permutive inversion inside the ZBL. -/
theorem zrow_inv (L : Nat → Bool) (t k : Nat) :
    zrow L t (k + 2) = xor (zrow L (t + 1) (k + 1)) (zrow L t (k + 1) || zrow L t k) := by
  rw [zrow_succ]; cases zrow L t (k + 2) <;> cases (zrow L t (k + 1) || zrow L t k) <;> rfl

/-- Shift in time: the ZBL is a semiflow. -/
theorem zrow_shift (L : Nat → Bool) (s : Nat) : ∀ t k, zrow L (s + t) k = zrow (zrow L s) t k := by
  intro t
  induction t with
  | zero =>
    intro k
    cases k with
    | zero => simp [zrow_zero_pos]
    | succ k => rfl
  | succ t ih =>
    intro k
    cases k with
    | zero => simp [zrow_zero_pos]
    | succ k =>
      rw [show s + (t + 1) = (s + t) + 1 by omega, zrow_succ, zrow_succ, ih, ih, ih]

/-! ## The reduction: period 2 gives a zero-boundary left half -/

theorem cell_congr' {t : Nat} {p q : Int} (h : p = q) : cell t p = cell t q := h ▸ rfl

theorem cell_step (t : Nat) (p : Int) :
    cell (t + 1) p = xor (cell t (p - 1)) (cell t p || cell t (p + 1)) := rfl

/-- Effective boundary: if the center is not black at both `t` and `t + 1`, then column `-1`
updates as if column `0` were white. -/
theorem cell_m1_step_of_noBB (t : Nat) (h : (center t && center (t + 1)) = false) :
    cell (t + 1) (-1) = xor (cell t (-2)) (cell t (-1)) := by
  rw [cell_step, cell_congr' (show (-1 : Int) - 1 = -2 by rfl),
    cell_congr' (show (-1 : Int) + 1 = 0 by rfl)]
  have hc : center (t + 1) = xor (cell t (-1)) (center t || cell t 1) := by
    show cell (t + 1) 0 = _
    rw [cell_step, cell_congr' (show (0 : Int) - 1 = -1 by rfl),
      cell_congr' (show (0 : Int) + 1 = 1 by rfl)]
    rfl
  unfold center at h hc
  cases h0 : cell t 0
  · simp
  · rw [h0] at h hc
    simp at h
    rw [h] at hc
    cases h1 : cell t (-1)
    · rw [h1] at hc; simp at hc
    · simp

/-- **The left half is a ZBL.** If `center t && center (t+1) = false` for all `t ≥ T`, then the
left half from time `T` on is the ZBL started from the row `k ↦ cell T (-k)`. -/
theorem cell_eq_zrow {T : Nat} (h : ∀ t, T ≤ t → (center t && center (t + 1)) = false) :
    ∀ t k, cell (T + t) (-((k + 1 : Nat) : Int)) = zrow (fun k => cell T (-(k : Int))) t (k + 1) := by
  intro t
  induction t with
  | zero => intro k; rfl
  | succ t ih =>
    intro k
    rw [zrow_succ, ← ih (k + 1), ← ih k, show T + (t + 1) = (T + t) + 1 by omega]
    cases k with
    | zero =>
      rw [zrow_zero_pos]
      rw [cell_congr' (show (-(((0 + 1 : Nat)) : Int)) = -1 by rfl),
        cell_congr' (show (-(((0 + 1 + 1 : Nat)) : Int)) = -2 by rfl),
        cell_m1_step_of_noBB (T + t) (h (T + t) (by omega))]
      simp
    | succ k =>
      rw [← ih (k), cell_step]
      rw [cell_congr' (show -(((k + 1 + 1 : Nat)) : Int) - 1 = -((k + 1 + 1 + 1 : Nat) : Int) by omega),
        cell_congr' (show -(((k + 1 + 1 : Nat)) : Int) + 1 = -((k + 1 : Nat) : Int) by omega)]

/-- The center column alternates from `T`, black first. -/
def Alt1 (T : Nat) : Prop := ∀ s, center (T + 2 * s) = true ∧ center (T + 2 * s + 1) = false

theorem noBB_of_alt1 {T : Nat} (h : Alt1 T) : ∀ t, T ≤ t → (center t && center (t + 1)) = false := by
  intro t ht
  obtain ⟨s, hs⟩ : ∃ s, t = T + 2 * s ∨ t = T + 2 * s + 1 := ⟨(t - T) / 2, by omega⟩
  rcases hs with hs | hs
  · subst hs; rw [(h s).2]; simp
  · subst hs; rw [(h s).2, show T + 2 * s + 1 + 1 = T + 2 * (s + 1) by omega]; simp

/-- Column `-1` is black whenever the center is black and turns white next. -/
theorem m1_black (t : Nat) (h0 : center t = true) (h1 : center (t + 1) = false) :
    cell t (-1) = true := by
  have hc : center (t + 1) = xor (cell t (-1)) (center t || cell t 1) := by
    show cell (t + 1) 0 = _
    rw [cell_step, cell_congr' (show (0 : Int) - 1 = -1 by rfl),
      cell_congr' (show (0 : Int) + 1 = 1 by rfl)]
    rfl
  rw [h0, h1] at hc
  cases h2 : cell t (-1)
  · rw [h2] at hc; simp at hc
  · rfl

/-- Constrained rows: column `1` of the ZBL is black at all even times. -/
def InX (L : Nat → Bool) : Prop := ∀ s, zrow L (2 * s) 1 = true

/-- Finitely supported rows. -/
def FinSupp (L : Nat → Bool) : Prop := ∃ W, ∀ k, W < k → L k = false

/-- **Q01**: no finitely supported row is constrained. -/
def Q01 : Prop := ∀ L : Nat → Bool, FinSupp L → ¬ InX L

theorem alt1_row_finSupp (T : Nat) : FinSupp (fun k => cell T (-(k : Int))) :=
  ⟨T, fun k hk => cell_eq_false_of_lt T _ (by omega)⟩

theorem alt1_row_inX {T : Nat} (h : Alt1 T) : InX (fun k => cell T (-(k : Int))) := by
  intro s
  have e := cell_eq_zrow (noBB_of_alt1 h) (2 * s) 0
  rw [← e, cell_congr' (show (-(((0 + 1 : Nat)) : Int)) = -1 by rfl)]
  exact m1_black _ (h s).1 (h s).2

theorem not_alt1_of_Q01 (hQ : Q01) (T : Nat) : ¬ Alt1 T :=
  fun h => hQ _ (alt1_row_finSupp T) (alt1_row_inX h)

/-- **Q01 rules out eventual period 2** (which includes eventual period 1): if `Q01` holds then the
center column has no transient `N` after which `center (t + 2) = center t`. -/
theorem no_period_two_of_Q01 (hQ : Q01) : ¬ ∃ N, ∀ t, N ≤ t → center (t + 2) = center t := by
  rintro ⟨N, hN⟩
  have hev : ∀ s, center (N + 2 * s) = center N ∧ center (N + 2 * s + 1) = center (N + 1) := by
    intro s
    induction s with
    | zero => exact ⟨rfl, rfl⟩
    | succ s ih =>
      constructor
      · rw [show N + 2 * (s + 1) = (N + 2 * s) + 2 by omega, hN _ (by omega), ih.1]
      · rw [show N + 2 * (s + 1) + 1 = (N + 2 * s + 1) + 2 by omega, hN _ (by omega), ih.2]
  cases h0 : center N <;> cases h1 : center (N + 1)
  · -- constant white
    refine center_not_eventually_constant ⟨N, false, fun t ht => ?_⟩
    obtain ⟨s, hs⟩ : ∃ s, t = N + 2 * s ∨ t = N + 2 * s + 1 := ⟨(t - N) / 2, by omega⟩
    rcases hs with hs | hs <;> subst hs
    · rw [(hev s).1, h0]
    · rw [(hev s).2, h1]
  · -- white then black: alternates from N + 1
    refine not_alt1_of_Q01 hQ (N + 1) (fun s => ⟨?_, ?_⟩)
    · rw [show N + 1 + 2 * s = N + 2 * s + 1 by omega, (hev s).2, h1]
    · rw [show N + 1 + 2 * s + 1 = N + 2 * (s + 1) by omega, (hev (s + 1)).1, h0]
  · -- black then white: alternates from N
    exact not_alt1_of_Q01 hQ N (fun s => ⟨by rw [(hev s).1, h0], by rw [(hev s).2, h1]⟩)
  · -- constant black
    refine center_not_eventually_constant ⟨N, true, fun t ht => ?_⟩
    obtain ⟨s, hs⟩ : ∃ s, t = N + 2 * s ∨ t = N + 2 * s + 1 := ⟨(t - N) / 2, by omega⟩
    rcases hs with hs | hs <;> subst hs
    · rw [(hev s).1, h0]
    · rw [(hev s).2, h1]

/-! ## The reconstruction map: the boundary column determines the row -/

/-- **Trace determination.** Position `k` at time `t` depends only on the boundary column at times
`t, …, t + k - 1`. -/
theorem zrow_det (L L' : Nat → Bool) :
    ∀ k t, (∀ i, i < k → zrow L (t + i) 1 = zrow L' (t + i) 1) → zrow L t k = zrow L' t k := by
  have key : ∀ k, (∀ t, (∀ i, i < k → zrow L (t + i) 1 = zrow L' (t + i) 1) →
      zrow L t k = zrow L' t k) ∧
      (∀ t, (∀ i, i < k + 1 → zrow L (t + i) 1 = zrow L' (t + i) 1) →
      zrow L t (k + 1) = zrow L' t (k + 1)) := by
    intro k
    induction k with
    | zero =>
      refine ⟨fun t _ => by rw [zrow_zero_pos, zrow_zero_pos], fun t h => ?_⟩
      have := h 0 (by omega)
      simpa using this
    | succ k ih =>
      refine ⟨ih.2, fun t h => ?_⟩
      rw [zrow_inv L t k, zrow_inv L' t k]
      have e1 : zrow L (t + 1) (k + 1) = zrow L' (t + 1) (k + 1) :=
        ih.2 (t + 1) fun i hi => by
          have := h (i + 1) (by omega)
          rwa [show t + (i + 1) = t + 1 + i by omega] at this
      have e2 : zrow L t (k + 1) = zrow L' t (k + 1) := ih.2 t fun i hi => h i (by omega)
      have e3 : zrow L t k = zrow L' t k := ih.1 t fun i hi => h i (by omega)
      rw [e1, e2, e3]
  exact fun k => (key k).1

/-- **Pivot structure.** If the boundary columns agree at times `t, …, t + k - 1`, then the rows at
time `t` differ at position `k + 1` exactly when the boundary columns differ at time `t + k`.
In particular the initial row `L(k + 1)` is the boundary value `y_k` xor a function of `y_0..y_{k-1}`. -/
theorem zrow_pivot (L L' : Nat → Bool) :
    ∀ k t, (∀ i, i < k → zrow L (t + i) 1 = zrow L' (t + i) 1) →
      xor (zrow L t (k + 1)) (zrow L' t (k + 1)) = xor (zrow L (t + k) 1) (zrow L' (t + k) 1) := by
  intro k
  induction k with
  | zero => intro t _; rfl
  | succ k ih =>
    intro t h
    rw [zrow_inv L t k, zrow_inv L' t k]
    have e2 : zrow L t (k + 1) = zrow L' t (k + 1) := zrow_det L L' (k + 1) t fun i hi => h i hi
    have e3 : zrow L t k = zrow L' t k := zrow_det L L' k t fun i hi => h i (by omega)
    have := ih (t + 1) fun i hi => by
      have := h (i + 1) (by omega)
      rwa [show t + (i + 1) = t + 1 + i by omega] at this
    rw [e2, e3, show t + (k + 1) = t + 1 + k by omega, ← this]
    cases zrow L (t + 1) (k + 1) <;> cases zrow L' (t + 1) (k + 1) <;>
      cases (zrow L' t (k + 1) || zrow L' t k) <;> rfl

/-- The spatial (left-permutive) reconstruction from a boundary column `y`:
`recon y k t` is the colour at position `k`, time `t`. -/
def recon (y : Nat → Bool) : Nat → Nat → Bool
  | 0, _ => false
  | 1, t => y t
  | k + 2, t => xor (recon y (k + 1) (t + 1)) (recon y (k + 1) t || recon y k t)

theorem zrow_recon (y : Nat → Bool) : ∀ t k, zrow (fun k => recon y k 0) t k = recon y k t := by
  intro t
  induction t with
  | zero =>
    intro k
    cases k with
    | zero => rfl
    | succ k => rfl
  | succ t ih =>
    intro k
    cases k with
    | zero => rfl
    | succ k =>
      rw [zrow_succ, ih, ih, ih]
      show _ = recon y (k + 1) (t + 1)
      have hdef : recon y (k + 2) t =
          xor (recon y (k + 1) (t + 1)) (recon y (k + 1) t || recon y k t) := by
        cases k <;> rfl
      rw [hdef]
      cases recon y (k + 1) (t + 1) <;> cases (recon y (k + 1) t || recon y k t) <;> rfl

/-- **The trace map is onto**: every boundary column is the boundary column of some row (and of only
one, by `zrow_det`). So the constrained rows are in bijection with the free-bit sequences `f`. -/
theorem trace_surj (y : Nat → Bool) : ∃ L : Nat → Bool, ∀ t, zrow L t 1 = y t :=
  ⟨fun k => recon y k 0, fun t => zrow_recon y t 1⟩

/-- The reconstruction map `Φ`: free bits `f` ↦ the unique constrained row with
`zrow L (2s+1) 1 = f s`. -/
def Phi (f : Nat → Bool) : Nat → Bool :=
  fun k => recon (fun t => if t % 2 = 0 then true else f (t / 2)) k 0

theorem Phi_inX (f : Nat → Bool) : InX (Phi f) := by
  intro s
  show zrow (fun k => recon (fun t => if t % 2 = 0 then true else f (t / 2)) k 0) (2 * s) 1 = true
  rw [zrow_recon]
  show (if 2 * s % 2 = 0 then true else f (2 * s / 2)) = true
  rw [if_pos (by omega)]

theorem Phi_free (f : Nat → Bool) (s : Nat) : zrow (Phi f) (2 * s + 1) 1 = f s := by
  show zrow (fun k => recon (fun t => if t % 2 = 0 then true else f (t / 2)) k 0) (2 * s + 1) 1 = f s
  rw [zrow_recon]
  show (if (2 * s + 1) % 2 = 0 then true else f ((2 * s + 1) / 2)) = f s
  rw [if_neg (by omega), show (2 * s + 1) / 2 = s by omega]

/-- `Q01` restated through `Φ`: no free-bit sequence gives a finitely supported row. -/
theorem Q01_iff_Phi : Q01 ↔ ∀ f, ¬ FinSupp (Phi f) := by
  constructor
  · intro hQ f hfin
    exact hQ _ hfin (Phi_inX f)
  · intro h L hfin hX
    let f : Nat → Bool := fun s => zrow L (2 * s + 1) 1
    have htr : ∀ k, (∀ i, i < k → zrow L (0 + i) 1 = zrow (Phi f) (0 + i) 1) := by
      intro k i _
      rw [Nat.zero_add]
      obtain ⟨s, hs⟩ : ∃ s, i = 2 * s ∨ i = 2 * s + 1 := ⟨i / 2, by omega⟩
      rcases hs with rfl | rfl
      · rw [hX s, Phi_inX f s]
      · rw [Phi_free f s]
    apply h f
    obtain ⟨W, hW⟩ := hfin
    refine ⟨W, fun k hk => ?_⟩
    have e := zrow_det L (Phi f) k 0 (htr k)
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    have e1 : zrow L 0 (k' + 1) = L (k' + 1) := rfl
    have e2 : zrow (Phi f) 0 (k' + 1) = Phi f (k' + 1) := rfl
    rw [← e2, ← e, e1]
    exact hW _ hk

/-! ## Identities forced by the constraint at small depth -/

/-- With `y₀ = y₂ = y₄ = 1` (`yᵢ = zrow L i 1`), writing `f₀ = y₁` and `f₁ = y₃`:
`L 2 = !f₀`, `L 3 = f₀`, `L 4 = !f₁`, `L 5 = f₀`. Hence `L 2 ≠ L 3` and `L 3 = L 5`. -/
theorem small_identities (L : Nat → Bool) (h0 : zrow L 0 1 = true) (h2 : zrow L 2 1 = true)
    (h4 : zrow L 4 1 = true) :
    L 2 = !zrow L 1 1 ∧ L 3 = zrow L 1 1 ∧ L 4 = !zrow L 3 1 ∧ L 5 = zrow L 1 1 := by
  have i02 : zrow L 0 2 = xor (zrow L 1 1) (zrow L 0 1 || zrow L 0 0) := zrow_inv L 0 0
  have i12 : zrow L 1 2 = xor (zrow L 2 1) (zrow L 1 1 || zrow L 1 0) := zrow_inv L 1 0
  have i22 : zrow L 2 2 = xor (zrow L 3 1) (zrow L 2 1 || zrow L 2 0) := zrow_inv L 2 0
  have i32 : zrow L 3 2 = xor (zrow L 4 1) (zrow L 3 1 || zrow L 3 0) := zrow_inv L 3 0
  have i03 : zrow L 0 3 = xor (zrow L 1 2) (zrow L 0 2 || zrow L 0 1) := zrow_inv L 0 1
  have i13 : zrow L 1 3 = xor (zrow L 2 2) (zrow L 1 2 || zrow L 1 1) := zrow_inv L 1 1
  have i23 : zrow L 2 3 = xor (zrow L 3 2) (zrow L 2 2 || zrow L 2 1) := zrow_inv L 2 1
  have i04 : zrow L 0 4 = xor (zrow L 1 3) (zrow L 0 3 || zrow L 0 2) := zrow_inv L 0 2
  have i14 : zrow L 1 4 = xor (zrow L 2 3) (zrow L 1 3 || zrow L 1 2) := zrow_inv L 1 2
  have i05 : zrow L 0 5 = xor (zrow L 1 4) (zrow L 0 4 || zrow L 0 3) := zrow_inv L 0 3
  simp only [zrow_zero_pos, Bool.or_false] at i02 i12 i22 i32
  have l2 : L 2 = zrow L 0 2 := rfl
  have l3 : L 3 = zrow L 0 3 := rfl
  have l4 : L 4 = zrow L 0 4 := rfl
  have l5 : L 5 = zrow L 0 5 := rfl
  rw [l2, l3, l4, l5, i05, i04, i14, i03, i13, i23, i02, i12, i22, i32, h0, h2, h4]
  cases zrow L 1 1 <;> cases zrow L 3 1 <;> decide

/-! ## A nonzero finite row never has an eventually periodic boundary column -/

/-- The edge of a finite row moves outward by one cell per step. -/
theorem zrow_edge (L : Nat → Bool) (W : Nat) (hW : L (W + 1) = true)
    (hz : ∀ k, W + 1 < k → L k = false) :
    ∀ t, zrow L t (W + 1 + t) = true ∧ ∀ k, W + 1 + t < k → zrow L t k = false := by
  intro t
  induction t with
  | zero =>
    refine ⟨hW, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    exact hz _ (by omega)
  | succ t ih =>
    refine ⟨?_, fun k hk => ?_⟩
    · rw [show W + 1 + (t + 1) = (W + 1 + t) + 1 by omega, zrow_succ,
        ih.2 _ (by omega), ih.2 _ (by omega), ih.1]
      rfl
    · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      rw [zrow_succ, ih.2 _ (by omega), ih.2 _ (by omega), ih.2 _ (by omega)]
      rfl

/-- **The boundary column of a nonzero finite ZBL row is not eventually periodic.** -/
theorem trace_not_eventuallyPeriodic (L : Nat → Bool) (W : Nat) (hW : L (W + 1) = true)
    (hz : ∀ k, W + 1 < k → L k = false) : ¬ EventuallyPeriodic (fun t => zrow L t 1) := by
  rintro ⟨N, P, hP, hper⟩
  have htr : ∀ i, i < W + N + P + 1 →
      zrow (zrow L N) (0 + i) 1 = zrow (zrow L (N + P)) (0 + i) 1 := by
    intro i _
    rw [← zrow_shift, ← zrow_shift, show N + (0 + i) = N + i by omega,
      show N + P + (0 + i) = (N + i) + P by omega]
    exact (hper (N + i) (by omega)).symm
  have e := zrow_det (zrow L N) (zrow L (N + P)) (W + N + P + 1) 0 htr
  have hA : zrow (zrow L N) 0 (W + N + P + 1) = zrow L N (W + N + P + 1) := rfl
  have hB : zrow (zrow L (N + P)) 0 (W + N + P + 1) = zrow L (N + P) (W + N + P + 1) := rfl
  rw [hA, hB, (zrow_edge L W hW hz N).2 _ (by omega),
    show W + N + P + 1 = W + 1 + (N + P) by omega, (zrow_edge L W hW hz (N + P)).1] at e
  exact absurd e (by decide)

/-- A finitely supported row with `L 1 = true` has a last black cell. -/
theorem last_one (L : Nat → Bool) (h1 : L 1 = true) :
    ∀ W, (∀ k, W < k → L k = false) → ∃ W', L (W' + 1) = true ∧ ∀ k, W' + 1 < k → L k = false := by
  intro W
  induction W with
  | zero => intro hz; exact absurd (hz 1 (by omega)) (by rw [h1]; decide)
  | succ W ih =>
    intro hz
    cases hW : L (W + 1)
    · exact ih fun k hk => by
        rcases Nat.lt_or_ge (W + 1) k with h | h
        · exact hz k h
        · rw [show k = W + 1 by omega]; exact hW
    · exact ⟨W, hW, fun k hk => hz k (by omega)⟩

/-- **Q01 for eventually periodic free bits.** If a finitely supported row is constrained, its free
bits `f_s = zrow L (2s+1) 1` are not eventually periodic. -/
theorem free_not_eventuallyPeriodic (L : Nat → Bool) (hfin : FinSupp L) (hX : InX L) :
    ¬ EventuallyPeriodic (fun s => zrow L (2 * s + 1) 1) := by
  rintro ⟨N, P, hP, hper⟩
  obtain ⟨W, hz⟩ := hfin
  have h1 : L 1 = true := hX 0
  obtain ⟨W', hW', hz'⟩ := last_one L h1 W hz
  refine trace_not_eventuallyPeriodic L W' hW' hz' ⟨2 * N, 2 * P, by omega, fun t ht => ?_⟩
  obtain ⟨s, hs⟩ : ∃ s, t = 2 * s ∨ t = 2 * s + 1 := ⟨t / 2, by omega⟩
  rcases hs with hs | hs <;> subst hs
  · show zrow L (2 * s + 2 * P) 1 = zrow L (2 * s) 1
    rw [show 2 * s + 2 * P = 2 * (s + P) by omega, hX, hX]
  · show zrow L (2 * s + 1 + 2 * P) 1 = zrow L (2 * s + 1) 1
    rw [show 2 * s + 1 + 2 * P = 2 * (s + P) + 1 by omega]
    exact hper s (by omega)

/-! ## Contrast: finite perturbations of the stripe stay confined -/

/-- The stripe `1010…` (black at odd positions), a fixed point of the ZBL. -/
def stripe (k : Nat) : Bool := k % 2 == 1

theorem stripe_fixed (k : Nat) :
    stripe (k + 1) = xor (stripe (k + 2)) (stripe (k + 1) || stripe k) := by
  unfold stripe
  rcases Nat.mod_two_eq_zero_or_one k with h | h
  · rw [show (k + 1) % 2 = 1 by omega, show (k + 2) % 2 = 0 by omega, h]; rfl
  · rw [show (k + 1) % 2 = 0 by omega, show (k + 2) % 2 = 1 by omega, h]; rfl

/-- **Stripe confinement.** If a row agrees with the stripe from an odd position `K` on, then so does
every later row: damage cannot cross the black stripe cell at `K` outward (the `or` is saturated). -/
theorem stripe_confined (L : Nat → Bool) (K : Nat) (hK : K % 2 = 1)
    (h : ∀ k, K ≤ k → L k = stripe k) : ∀ t k, K ≤ k → zrow L t k = stripe k := by
  intro t
  induction t with
  | zero =>
    intro k hk
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    exact h _ hk
  | succ t ih =>
    intro k hk
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [zrow_succ, ih (k' + 2) (by omega), ih (k' + 1) hk]
    rcases Nat.lt_or_ge K (k' + 1) with hlt | hge
    · rw [ih k' (by omega)]; exact (stripe_fixed k').symm
    · have hKe : k' + 1 = K := by omega
      have hs : stripe (k' + 1) = true := by unfold stripe; rw [hKe, hK]; rfl
      have hs2 : stripe (k' + 2) = false := by
        unfold stripe; rw [show (k' + 2) % 2 = 0 by omega]; rfl
      rw [hs, hs2]; rfl

/-- Consequently a row that agrees with the stripe from an odd position on has an eventually
periodic boundary column (its orbit lives in a finite set). -/
theorem stripe_tail_trace_periodic (L : Nat → Bool) (K : Nat) (hK : K % 2 = 1)
    (h : ∀ k, K ≤ k → L k = stripe k) : EventuallyPeriodic (fun t => zrow L t 1) := by
  let a : Nat → List Bool := fun m => (List.range K).map (fun k => zrow L m k)
  obtain ⟨m, n, hmn, -, he⟩ := pigeonhole K a (fun m => by simp [a])
  have hrow : ∀ k, zrow L m k = zrow L n k := by
    intro k
    rcases Nat.lt_or_ge k K with hk | hk
    · have := congrArg (fun l => l[k]?) he
      simpa [a, hk] using this
    · rw [stripe_confined L K hK h m k hk, stripe_confined L K hK h n k hk]
  refine ⟨m, n - m, by omega, fun t ht => ?_⟩
  have e1 : zrow L (t + (n - m)) 1 = zrow (zrow L n) (t - m) 1 := by
    rw [← zrow_shift, show n + (t - m) = t + (n - m) by omega]
  have e2 : zrow L t 1 = zrow (zrow L m) (t - m) 1 := by
    rw [← zrow_shift, show m + (t - m) = t by omega]
  have hfun : zrow L m = zrow L n := funext hrow
  show zrow L (t + (n - m)) 1 = zrow L t 1
  rw [e1, e2, hfun]

/-! ## Stripe absorption: a stripe tail swallows the whole row

The stripe front advances inward by two cells within at most `9` steps, whatever lies inside it
(a local check over the `2 ^ 11` configurations of the eleven cells inside the front, done by
`decide`), and strips of at most `10` inner cells reach the stripe (another `decide`). Together with
`stripe_confined` this proves that every row which agrees with the stripe from an odd position on
reaches the stripe exactly; in particular its boundary column is eventually all black. -/

/-- Cells `1..n` of a row packed into the bits `1..n` of a natural number. -/
def enc (R : Nat → Bool) : Nat → Nat
  | 0 => 0
  | n + 1 => enc R n ||| (if R (n + 1) then 1 <<< (n + 1) else 0)

/-- Bits `1..n`. -/
def smask (n : Nat) : Nat := ((1 <<< n) - 1) <<< 1

/-- The strip `1..n` with a white cell at `0` and a black cell at `n + 1`. -/
def sextN (n v : Nat) : Nat := (v &&& smask n) ||| (1 <<< (n + 1))

/-- One ZBL step of the strip `1..n` closed by a black cell at `n + 1`. -/
def bstep (n v : Nat) : Nat :=
  ((sextN n v >>> 1) ^^^ (sextN n v ||| (sextN n v <<< 1))) &&& smask n

def biter (n : Nat) : Nat → Nat → Nat
  | 0, v => v
  | s + 1, v => biter n s (bstep n v)

def frontWithin (n : Nat) : Nat → Nat → Bool
  | 0, v => v.testBit (n - 1) && !v.testBit n
  | f + 1, v => (v.testBit (n - 1) && !v.testBit n) || frontWithin n f (bstep n v)

def reachesStripe (n : Nat) : Nat → Nat → Bool
  | 0, v => v == enc stripe n
  | f + 1, v => v == enc stripe n || reachesStripe n f (bstep n v)

def allBelow (p : Nat → Bool) : Nat → Bool
  | 0 => true
  | N + 1 => p N && allBelow p N

/-- Local front check: with the stripe from cell `13` on, cells `11, 12` become `1, 0` within
`9` steps, for each of the `2 ^ 12` contents of cells `1..12`. -/
theorem front_check : allBelow (fun v => v % 2 == 1 || frontWithin 12 9 v) (2 ^ 13) = true := by
  decide +kernel

/-- Small strips: with the stripe from cell `11` on, every content of cells `1..10` reaches the
stripe within `40` steps. -/
theorem small_check : allBelow (fun v => v % 2 == 1 || reachesStripe 10 40 v) (2 ^ 11) = true := by
  decide +kernel

theorem allBelow_spec (p : Nat → Bool) : ∀ N, allBelow p N = true → ∀ c, c < N → p c = true := by
  intro N
  induction N with
  | zero => intro _ c hc; omega
  | succ N ih =>
    intro h c hc
    simp only [allBelow, Bool.and_eq_true] at h
    rcases Nat.lt_or_ge c N with h' | h'
    · exact ih h.2 c h'
    · rw [show c = N by omega]; exact h.1

theorem testBit_enc (R : Nat → Bool) :
    ∀ n i, (enc R n).testBit i = (decide (1 ≤ i) && decide (i ≤ n) && R i) := by
  intro n
  induction n with
  | zero =>
    intro i
    simp only [enc, Nat.zero_testBit]
    by_cases h : 1 ≤ i <;> simp [h] <;> omega
  | succ n ih =>
    intro i
    simp only [enc, Nat.testBit_or, ih]
    cases hR : R (n + 1)
    · simp only [Bool.false_eq_true, ↓reduceIte, Nat.zero_testBit, Bool.or_false]
      by_cases h1 : i = n + 1
      · subst h1; simp [hR]
      · by_cases h2 : i ≤ n
        · simp [h2, show i ≤ n + 1 by omega]
        · simp [h2, show ¬ i ≤ n + 1 by omega]
    · simp only [↓reduceIte, Nat.one_shiftLeft, Nat.testBit_two_pow]
      by_cases h1 : i = n + 1
      · subst h1; simp [hR]
      · by_cases h2 : i ≤ n
        · simp [h2, show i ≤ n + 1 by omega, show n + 1 ≠ i by omega]
        · simp [h2, show ¬ i ≤ n + 1 by omega, show n + 1 ≠ i by omega]

theorem testBit_smask (n i : Nat) : (smask n).testBit i = (decide (1 ≤ i) && decide (i ≤ n)) := by
  unfold smask
  rw [Nat.testBit_shiftLeft, Nat.one_shiftLeft, Nat.testBit_two_pow_sub_one]
  by_cases h : 1 ≤ i
  · simp only [show i ≥ 1 from h, decide_true, Bool.true_and]
    by_cases h2 : i ≤ n
    · simp [h2]; omega
    · simp [h2]; omega
  · simp [h]

theorem testBit_sextN (n v i : Nat) :
    (sextN n v).testBit i = ((decide (1 ≤ i) && decide (i ≤ n) && v.testBit i) || decide (i = n + 1)) := by
  unfold sextN
  rw [Nat.testBit_or, Nat.testBit_and, testBit_smask, Nat.one_shiftLeft, Nat.testBit_two_pow]
  by_cases h : i = n + 1
  · subst h; simp
  · simp only [h, show ¬ (n + 1 = i) by omega, decide_false, Bool.or_false]
    cases v.testBit i <;> cases decide (1 ≤ i) <;> cases decide (i ≤ n) <;> rfl

theorem testBit_bstep (n v i : Nat) :
    (bstep n v).testBit i = (decide (1 ≤ i) && decide (i ≤ n) &&
      xor ((sextN n v).testBit (i + 1))
        ((sextN n v).testBit i || (decide (1 ≤ i) && (sextN n v).testBit (i - 1)))) := by
  unfold bstep
  rw [Nat.testBit_and, Nat.testBit_xor, Nat.testBit_or, Nat.testBit_shiftRight, Nat.testBit_shiftLeft,
    testBit_smask, show 1 + i = i + 1 by omega]
  by_cases h : 1 ≤ i
  · simp [show i ≥ 1 from h]; cases decide (i ≤ n) <;> simp
  · simp [h]

/-- The packed strip of a row whose cell `n + 1` is black reads the row correctly on `0..n+1`. -/
theorem sextN_enc (R : Nat → Bool) (n : Nat) (hR : R (n + 1) = true) (h0 : R 0 = false) :
    ∀ j, j ≤ n + 1 → (sextN n (enc R n)).testBit j = R j := by
  intro j hj
  rw [testBit_sextN, testBit_enc]
  by_cases h1 : j = n + 1
  · subst h1; simp [hR]
  · by_cases h2 : j = 0
    · subst h2; simp [h0]
    · simp [show 1 ≤ j by omega, show j ≤ n by omega, h1]

theorem enc_step (R : Nat → Bool) (n t : Nat) (hR : zrow R t (n + 1) = true) :
    enc (zrow R (t + 1)) n = bstep n (enc (zrow R t) n) := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [testBit_enc, testBit_bstep]
  by_cases hi : 1 ≤ i ∧ i ≤ n
  · obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
    have e := sextN_enc (zrow R t) n hR (zrow_zero_pos R t)
    rw [e (i' + 1 + 1) (by omega), e (i' + 1) (by omega), show i' + 1 - 1 = i' by omega,
      e i' (by omega), zrow_succ]
    simp [show i' + 1 ≤ n by omega]
  · by_cases h1 : 1 ≤ i
    · simp [h1, show ¬ i ≤ n by omega]
    · simp [h1]

theorem enc_congr (R R' : Nat → Bool) (n : Nat) (h : ∀ k, 1 ≤ k → k ≤ n → R k = R' k) :
    enc R n = enc R' n := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [testBit_enc, testBit_enc]
  by_cases hi : 1 ≤ i ∧ i ≤ n
  · rw [h i hi.1 hi.2]
  · by_cases h1 : 1 ≤ i
    · simp [h1, show ¬ i ≤ n by omega]
    · simp [h1]

theorem biter_enc (R : Nat → Bool) (n : Nat) (hR : ∀ t, zrow R t (n + 1) = true) :
    ∀ s t, biter n s (enc (zrow R t) n) = enc (zrow R (t + s)) n := by
  intro s
  induction s with
  | zero => intro t; rfl
  | succ s ih =>
    intro t
    show biter n s (bstep n (enc (zrow R t) n)) = _
    rw [← enc_step R n t (hR t), ih, show t + 1 + s = t + (s + 1) by omega]

theorem frontWithin_spec (n : Nat) : ∀ f v, frontWithin n f v = true →
    ∃ s, s ≤ f ∧ (biter n s v).testBit (n - 1) = true ∧ (biter n s v).testBit n = false := by
  intro f
  induction f with
  | zero =>
    intro v h
    simp only [frontWithin, Bool.and_eq_true, Bool.not_eq_true'] at h
    exact ⟨0, Nat.le_refl 0, h.1, h.2⟩
  | succ f ih =>
    intro v h
    simp only [frontWithin, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at h
    rcases h with h | h
    · exact ⟨0, by omega, h.1, h.2⟩
    · obtain ⟨s, hs, h1, h2⟩ := ih _ h
      exact ⟨s + 1, by omega, h1, h2⟩

theorem reachesStripe_spec (n : Nat) : ∀ f v, reachesStripe n f v = true →
    ∃ s, s ≤ f ∧ biter n s v = enc stripe n := by
  intro f
  induction f with
  | zero =>
    intro v h
    simp only [reachesStripe, beq_iff_eq] at h
    exact ⟨0, Nat.le_refl 0, h⟩
  | succ f ih =>
    intro v h
    simp only [reachesStripe, Bool.or_eq_true, beq_iff_eq] at h
    rcases h with h | h
    · exact ⟨0, by omega, h⟩
    · obtain ⟨s, hs, h1⟩ := ih _ h
      exact ⟨s + 1, by omega, h1⟩

theorem enc_lt (R : Nat → Bool) (n : Nat) : enc R n < 2 ^ (n + 1) :=
  Nat.lt_pow_two_of_testBit _ fun i hi => by rw [testBit_enc]; simp [show ¬ i ≤ n by omega]

theorem enc_even (R : Nat → Bool) (n : Nat) : enc R n % 2 = 0 := by
  have h := testBit_enc R n 0
  rw [Nat.testBit_zero] at h
  simp at h
  omega

/-- Base front lemma: stripe from `13` on gives cells `11, 12 = 1, 0` within `9` steps. -/
theorem front_base (R : Nat → Bool) (h : ∀ k, 13 ≤ k → R k = stripe k) :
    ∃ s, s ≤ 9 ∧ zrow R s 11 = true ∧ zrow R s 12 = false := by
  have hc := stripe_confined R 13 (by decide) h
  have h13 : ∀ t, zrow R t (12 + 1) = true := fun t => hc t 13 (by omega)
  have hv := allBelow_spec _ _ front_check (enc R 12) (enc_lt R 12)
  simp only [Bool.or_eq_true, beq_iff_eq, enc_even] at hv
  have hv' : frontWithin 12 9 (enc R 12) = true := by
    rcases hv with hv | hv
    · exact absurd hv (by decide)
    · exact hv
  obtain ⟨s, hs, h1, h2⟩ := frontWithin_spec 12 9 _ hv'
  have e0 : enc R 12 = enc (zrow R 0) 12 := enc_congr _ _ _ fun k hk _ => by
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rfl
  rw [e0, biter_enc R 12 h13, Nat.zero_add, testBit_enc] at h1 h2
  refine ⟨s, hs, ?_, ?_⟩
  · simpa using h1
  · simpa using h2

/-- Locality on the outer side: rows agreeing from `a ≥ 1` on agree at time `s` from `a + s` on. -/
theorem zrow_local (L L' : Nat → Bool) (a : Nat) (ha : 1 ≤ a) (h : ∀ k, a ≤ k → L k = L' k) :
    ∀ s k, a + s ≤ k → zrow L s k = zrow L' s k := by
  intro s
  induction s with
  | zero =>
    intro k hk
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    exact h _ (by omega)
  | succ s ih =>
    intro k hk
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [zrow_succ, zrow_succ, ih (k' + 2) (by omega), ih (k' + 1) (by omega), ih k' (by omega)]

/-- Move a row `d` cells outward (cells `1..d` white). -/
def shiftOut (d : Nat) (L : Nat → Bool) (k : Nat) : Bool := if k ≤ d then false else L (k - d)

/-- Away from the boundary's light cone, the outward-shifted row evolves like the original. -/
theorem zrow_shiftOut (L : Nat → Bool) (d : Nat) :
    ∀ s k, s ≤ k → zrow (shiftOut d L) s (k + d) = zrow L s k := by
  intro s
  induction s with
  | zero =>
    intro k _
    cases k with
    | zero =>
      cases d with
      | zero => rfl
      | succ d => show shiftOut (d + 1) L (0 + (d + 1)) = false; simp [shiftOut]
    | succ k =>
      rw [show k + 1 + d = (k + d) + 1 by omega]
      show shiftOut d L (k + d + 1) = L (k + 1)
      simp [shiftOut, show ¬ (k + d + 1 ≤ d) by omega, show k + d + 1 - d = k + 1 by omega]
  | succ s ih =>
    intro k hk
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [show k' + 1 + d = (k' + d) + 1 by omega, zrow_succ, zrow_succ,
      show k' + d + 2 = (k' + 2) + d by omega, show k' + d + 1 = (k' + 1) + d by omega,
      ih (k' + 2) (by omega), ih (k' + 1) (by omega), ih k' (by omega)]

theorem stripe_add_even (k d : Nat) (hd : d % 2 = 0) : stripe (k + d) = stripe k := by
  unfold stripe
  rw [show (k + d) % 2 = k % 2 by omega]

/-- **Front lemma.** If a row agrees with the stripe from an odd position `m ≥ 13` on, then within
`9` steps it agrees with the stripe from `m - 2` on. -/
theorem front_advance (R : Nat → Bool) (m : Nat) (hm : m % 2 = 1) (hm13 : 13 ≤ m)
    (h : ∀ k, m ≤ k → R k = stripe k) :
    ∃ s, s ≤ 9 ∧ ∀ k, m - 2 ≤ k → zrow R s k = stripe k := by
  obtain ⟨d, rfl⟩ : ∃ d, m = 13 + d := ⟨m - 13, by omega⟩
  have hd : d % 2 = 0 := by omega
  let B : Nat → Bool := fun k => R (k + d)
  have hB : ∀ k, 13 ≤ k → B k = stripe k := fun k hk => by
    show R (k + d) = stripe k
    rw [h (k + d) (by omega), stripe_add_even k d hd]
  obtain ⟨s, hs, h1, h2⟩ := front_base B hB
  have hagree : ∀ k, d + 1 ≤ k → R k = shiftOut d B k := fun k hk => by
    simp [shiftOut, show ¬ k ≤ d by omega, B, show k - d + d = k by omega]
  have loc := zrow_local R (shiftOut d B) (d + 1) (by omega) hagree s
  have e11 : zrow R s (11 + d) = zrow B s 11 := by
    rw [loc (11 + d) (by omega), zrow_shiftOut B d s 11 (by omega)]
  have e12 : zrow R s (12 + d) = zrow B s 12 := by
    rw [loc (12 + d) (by omega), zrow_shiftOut B d s 12 (by omega)]
  have hc := stripe_confined R (13 + d) (by omega) h s
  refine ⟨s, hs, fun k hk => ?_⟩
  rcases Nat.lt_or_ge k (13 + d) with hk' | hk'
  · rcases (show k = 11 + d ∨ k = 12 + d by omega) with rfl | rfl
    · rw [e11, h1]; unfold stripe; rw [show (11 + d) % 2 = 1 by omega]; rfl
    · rw [e12, h2]; unfold stripe; rw [show (12 + d) % 2 = 0 by omega]; rfl
  · exact hc k hk'

/-- Base of the descent: a stripe from `11` on reaches the stripe everywhere within `40` steps. -/
theorem small_base (R : Nat → Bool) (h : ∀ k, 11 ≤ k → R k = stripe k) :
    ∃ s, s ≤ 40 ∧ ∀ k, 1 ≤ k → zrow R s k = stripe k := by
  have hc := stripe_confined R 11 (by decide) h
  have h11 : ∀ t, zrow R t (10 + 1) = true := fun t => hc t 11 (by omega)
  have hv := allBelow_spec _ _ small_check (enc R 10) (enc_lt R 10)
  simp only [Bool.or_eq_true, beq_iff_eq, enc_even] at hv
  have hv' : reachesStripe 10 40 (enc R 10) = true := by
    rcases hv with hv | hv
    · exact absurd hv (by decide)
    · exact hv
  obtain ⟨s, hs, he⟩ := reachesStripe_spec 10 40 _ hv'
  have e0 : enc R 10 = enc (zrow R 0) 10 := enc_congr _ _ _ fun k hk _ => by
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rfl
  rw [e0, biter_enc R 10 h11, Nat.zero_add] at he
  refine ⟨s, hs, fun k hk => ?_⟩
  rcases Nat.lt_or_ge k 11 with hk' | hk'
  · have := congrArg (fun v => Nat.testBit v k) he
    simp only [testBit_enc] at this
    simpa [hk, show k ≤ 10 by omega] using this
  · exact hc s k hk'

/-- **Stripe absorption.** A ZBL row that agrees with the stripe `1010…` from some odd position on
becomes exactly the stripe after finitely many steps and stays there. -/
theorem stripe_absorb (R : Nat → Bool) (m : Nat) (hm : m % 2 = 1) (h : ∀ k, m ≤ k → R k = stripe k) :
    ∃ T, ∀ t, T ≤ t → ∀ k, 1 ≤ k → zrow R t k = stripe k := by
  -- descent: reach a stripe from 11 on
  have desc : ∀ j (R : Nat → Bool), (∀ k, 11 + 2 * j ≤ k → R k = stripe k) →
      ∃ T, ∀ k, 11 ≤ k → zrow R T k = stripe k := by
    intro j
    induction j with
    | zero => intro R hR; exact ⟨0, fun k hk => by
        obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
        exact hR _ hk⟩
    | succ j ih =>
      intro R hR
      obtain ⟨s, -, hs⟩ := front_advance R (11 + 2 * (j + 1)) (by omega) (by omega) hR
      obtain ⟨T, hT⟩ := ih (zrow R s) fun k hk => hs k (by omega)
      exact ⟨s + T, fun k hk => by rw [zrow_shift]; exact hT k hk⟩
  obtain ⟨T₁, hT₁⟩ := desc (m / 2) R fun k hk => h k (by omega)
  obtain ⟨s, -, hs⟩ := small_base (zrow R T₁) hT₁
  refine ⟨T₁ + s, fun t ht k hk => ?_⟩
  have hfull : ∀ k, 1 ≤ k → zrow R (T₁ + s) k = stripe k := fun k hk => by
    rw [zrow_shift]; exact hs k hk
  have := stripe_confined (zrow R (T₁ + s)) 1 (by decide) hfull (t - (T₁ + s)) k hk
  rwa [← zrow_shift, show T₁ + s + (t - (T₁ + s)) = t by omega] at this

/-- Consequently a constrained row with a stripe tail has free bits that are eventually all `1`
(it is eventually the fixed point `Φ(1^∞)`). -/
theorem stripe_tail_free_eventually_one (R : Nat → Bool) (m : Nat) (hm : m % 2 = 1)
    (h : ∀ k, m ≤ k → R k = stripe k) : ∃ T, ∀ t, T ≤ t → zrow R t 1 = true := by
  obtain ⟨T, hT⟩ := stripe_absorb R m hm h
  exact ⟨T, fun t ht => hT t ht 1 (Nat.le_refl 1)⟩

/-! ### The other stripe phase

The stripe black at even positions is a fixed point away from the boundary; at the boundary cell `1`
then alternates (the 2-cycle `11(01)^∞ ↔ (01)^∞`, which is `Φ(0^∞)` and its image). The same front
mechanism shows that a tail in this phase absorbs everything except cell `1`. -/

/-- The stripe black at even positions. -/
def stripe2 (k : Nat) : Bool := k % 2 == 0

theorem stripe2_fixed (k : Nat) :
    stripe2 (k + 1) = xor (stripe2 (k + 2)) (stripe2 (k + 1) || stripe2 k) := by
  unfold stripe2
  rcases Nat.mod_two_eq_zero_or_one k with h | h
  · rw [show (k + 1) % 2 = 1 by omega, show (k + 2) % 2 = 0 by omega, h]; rfl
  · rw [show (k + 1) % 2 = 0 by omega, show (k + 2) % 2 = 1 by omega, h]; rfl

theorem stripe2_confined (L : Nat → Bool) (K : Nat) (hK : K % 2 = 0) (hK2 : 2 ≤ K)
    (h : ∀ k, K ≤ k → L k = stripe2 k) : ∀ t k, K ≤ k → zrow L t k = stripe2 k := by
  intro t
  induction t with
  | zero =>
    intro k hk
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    exact h _ hk
  | succ t ih =>
    intro k hk
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [zrow_succ, ih (k' + 2) (by omega), ih (k' + 1) hk]
    rcases Nat.lt_or_ge K (k' + 1) with hlt | hge
    · rw [ih k' (by omega)]; exact (stripe2_fixed k').symm
    · have hKe : k' + 1 = K := by omega
      have hs : stripe2 (k' + 1) = true := by unfold stripe2; rw [hKe, hK]; rfl
      have hs2 : stripe2 (k' + 2) = false := by
        unfold stripe2; rw [show (k' + 2) % 2 = 1 by omega]; rfl
      rw [hs, hs2]; rfl

/-- Local front check for the even phase: stripe from cell `14` on, cells `12, 13` become `1, 0`
within `9` steps, for each of the `2 ^ 13` contents of cells `1..13`. -/
theorem front_check2 : allBelow (fun v => v % 2 == 1 || frontWithin 13 9 v) (2 ^ 14) = true := by
  decide +kernel

def reachesStripe2 (n : Nat) : Nat → Nat → Bool
  | 0, v => v >>> 2 == enc stripe2 n >>> 2
  | f + 1, v => v >>> 2 == enc stripe2 n >>> 2 || reachesStripe2 n f (bstep n v)

/-- Small strips, even phase: stripe from cell `12` on; every content of cells `1..11` reaches the
stripe on cells `2..11` within `40` steps. -/
theorem small_check2 : allBelow (fun v => v % 2 == 1 || reachesStripe2 11 40 v) (2 ^ 12) = true := by
  decide +kernel

theorem reachesStripe2_spec (n : Nat) : ∀ f v, reachesStripe2 n f v = true →
    ∃ s, s ≤ f ∧ biter n s v >>> 2 = enc stripe2 n >>> 2 := by
  intro f
  induction f with
  | zero =>
    intro v h
    simp only [reachesStripe2, beq_iff_eq] at h
    exact ⟨0, Nat.le_refl 0, h⟩
  | succ f ih =>
    intro v h
    simp only [reachesStripe2, Bool.or_eq_true, beq_iff_eq] at h
    rcases h with h | h
    · exact ⟨0, by omega, h⟩
    · obtain ⟨s, hs, h1⟩ := ih _ h
      exact ⟨s + 1, by omega, h1⟩

theorem front_base2 (R : Nat → Bool) (h : ∀ k, 14 ≤ k → R k = stripe2 k) :
    ∃ s, s ≤ 9 ∧ zrow R s 12 = true ∧ zrow R s 13 = false := by
  have hc := stripe2_confined R 14 (by decide) (by decide) h
  have h14 : ∀ t, zrow R t (13 + 1) = true := fun t => hc t 14 (by omega)
  have hv := allBelow_spec _ _ front_check2 (enc R 13) (enc_lt R 13)
  simp only [Bool.or_eq_true, beq_iff_eq, enc_even] at hv
  have hv' : frontWithin 13 9 (enc R 13) = true := by
    rcases hv with hv | hv
    · exact absurd hv (by decide)
    · exact hv
  obtain ⟨s, hs, h1, h2⟩ := frontWithin_spec 13 9 _ hv'
  have e0 : enc R 13 = enc (zrow R 0) 13 := enc_congr _ _ _ fun k hk _ => by
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rfl
  rw [e0, biter_enc R 13 h14, Nat.zero_add, testBit_enc] at h1 h2
  refine ⟨s, hs, ?_, ?_⟩
  · simpa using h1
  · simpa using h2

theorem stripe2_add_even (k d : Nat) (hd : d % 2 = 0) : stripe2 (k + d) = stripe2 k := by
  unfold stripe2
  rw [show (k + d) % 2 = k % 2 by omega]

theorem front_advance2 (R : Nat → Bool) (m : Nat) (hm : m % 2 = 0) (hm14 : 14 ≤ m)
    (h : ∀ k, m ≤ k → R k = stripe2 k) :
    ∃ s, s ≤ 9 ∧ ∀ k, m - 2 ≤ k → zrow R s k = stripe2 k := by
  obtain ⟨d, rfl⟩ : ∃ d, m = 14 + d := ⟨m - 14, by omega⟩
  have hd : d % 2 = 0 := by omega
  let B : Nat → Bool := fun k => R (k + d)
  have hB : ∀ k, 14 ≤ k → B k = stripe2 k := fun k hk => by
    show R (k + d) = stripe2 k
    rw [h (k + d) (by omega), stripe2_add_even k d hd]
  obtain ⟨s, hs, h1, h2⟩ := front_base2 B hB
  have hagree : ∀ k, d + 1 ≤ k → R k = shiftOut d B k := fun k hk => by
    simp [shiftOut, show ¬ k ≤ d by omega, B, show k - d + d = k by omega]
  have loc := zrow_local R (shiftOut d B) (d + 1) (by omega) hagree s
  have e12 : zrow R s (12 + d) = zrow B s 12 := by
    rw [loc (12 + d) (by omega), zrow_shiftOut B d s 12 (by omega)]
  have e13 : zrow R s (13 + d) = zrow B s 13 := by
    rw [loc (13 + d) (by omega), zrow_shiftOut B d s 13 (by omega)]
  have hc := stripe2_confined R (14 + d) (by omega) (by omega) h s
  refine ⟨s, hs, fun k hk => ?_⟩
  rcases Nat.lt_or_ge k (14 + d) with hk' | hk'
  · rcases (show k = 12 + d ∨ k = 13 + d by omega) with rfl | rfl
    · rw [e12, h1]; unfold stripe2; rw [show (12 + d) % 2 = 0 by omega]; rfl
    · rw [e13, h2]; unfold stripe2; rw [show (13 + d) % 2 = 1 by omega]; rfl
  · exact hc k hk'

theorem small_base2 (R : Nat → Bool) (h : ∀ k, 12 ≤ k → R k = stripe2 k) :
    ∃ s, s ≤ 40 ∧ ∀ k, 2 ≤ k → zrow R s k = stripe2 k := by
  have hc := stripe2_confined R 12 (by decide) (by decide) h
  have h12 : ∀ t, zrow R t (11 + 1) = true := fun t => hc t 12 (by omega)
  have hv := allBelow_spec _ _ small_check2 (enc R 11) (enc_lt R 11)
  simp only [Bool.or_eq_true, beq_iff_eq, enc_even] at hv
  have hv' : reachesStripe2 11 40 (enc R 11) = true := by
    rcases hv with hv | hv
    · exact absurd hv (by decide)
    · exact hv
  obtain ⟨s, hs, he⟩ := reachesStripe2_spec 11 40 _ hv'
  have e0 : enc R 11 = enc (zrow R 0) 11 := enc_congr _ _ _ fun k hk _ => by
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rfl
  rw [e0, biter_enc R 11 h12, Nat.zero_add] at he
  refine ⟨s, hs, fun k hk => ?_⟩
  rcases Nat.lt_or_ge k 12 with hk' | hk'
  · have := congrArg (fun v => Nat.testBit v (k - 2)) he
    simp only [Nat.testBit_shiftRight, testBit_enc, show 2 + (k - 2) = k by omega] at this
    simpa [show 1 ≤ k by omega, show k ≤ 11 by omega] using this
  · exact hc s k hk'

/-- **Stripe absorption, even phase.** A row that agrees with the even-phase stripe from some
position on agrees with it on all cells `k ≥ 2` after finitely many steps; cell `1` then alternates. -/
theorem stripe2_absorb (R : Nat → Bool) (m : Nat) (hm : m % 2 = 0) (h : ∀ k, m ≤ k → R k = stripe2 k) :
    ∃ T, ∀ t, T ≤ t → (∀ k, 2 ≤ k → zrow R t k = stripe2 k) ∧ zrow R (t + 1) 1 = !zrow R t 1 := by
  have desc : ∀ j (R : Nat → Bool), (∀ k, 12 + 2 * j ≤ k → R k = stripe2 k) →
      ∃ T, ∀ k, 12 ≤ k → zrow R T k = stripe2 k := by
    intro j
    induction j with
    | zero => intro R hR; exact ⟨0, fun k hk => by
        obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
        exact hR _ hk⟩
    | succ j ih =>
      intro R hR
      obtain ⟨s, -, hs⟩ := front_advance2 R (12 + 2 * (j + 1)) (by omega) (by omega) hR
      obtain ⟨T, hT⟩ := ih (zrow R s) fun k hk => hs k (by omega)
      exact ⟨s + T, fun k hk => by rw [zrow_shift]; exact hT k hk⟩
  obtain ⟨T₁, hT₁⟩ := desc (m / 2) R fun k hk => h k (by omega)
  obtain ⟨s, -, hs⟩ := small_base2 (zrow R T₁) hT₁
  have hfull : ∀ k, 2 ≤ k → zrow R (T₁ + s) k = stripe2 k := fun k hk => by
    rw [zrow_shift]; exact hs k hk
  have hall : ∀ t, T₁ + s ≤ t → ∀ k, 2 ≤ k → zrow R t k = stripe2 k := by
    intro t ht k hk
    have := stripe2_confined (zrow R (T₁ + s)) 2 (by decide) (by decide)
      (fun k hk => by obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩; exact hfull _ hk)
      (t - (T₁ + s)) k hk
    rwa [← zrow_shift, show T₁ + s + (t - (T₁ + s)) = t by omega] at this
  refine ⟨T₁ + s, fun t ht => ⟨hall t ht, ?_⟩⟩
  have h2 : zrow R t 2 = true := by rw [hall t ht 2 (by omega)]; rfl
  rw [show (1 : Nat) = 0 + 1 from rfl, zrow_succ, h2, zrow_zero_pos]
  cases zrow R t (0 + 1) <;> rfl

/-- A constrained row with an even-phase stripe tail has free bits that are eventually all `0`. -/
theorem stripe2_tail_free_eventually_zero (R : Nat → Bool) (hX : InX R) (m : Nat) (hm : m % 2 = 0)
    (h : ∀ k, m ≤ k → R k = stripe2 k) : ∃ S, ∀ s, S ≤ s → zrow R (2 * s + 1) 1 = false := by
  obtain ⟨T, hT⟩ := stripe2_absorb R m hm h
  refine ⟨T, fun s hs => ?_⟩
  rw [(hT (2 * s) (by omega)).2, hX s]
  rfl

end R30ZBL

namespace R30ZBLCheck
open Ruliology.CellularAutomata
open Ruliology.CellularAutomata.Rule30Jen
open Ruliology.CellularAutomata.Rule30Prize
open R30ZBL

/-- Independent corollary: Q01 excludes every eventual period dividing 2, any transient. -/
theorem no_period_dvd_two_of_Q01 (hQ : Q01) :
    ∀ T P, 0 < P → P ∣ 2 → ¬ ∀ t, T ≤ t → center (t + P) = center t := by
  intro T P hP hd hper
  have hP12 : P = 1 ∨ P = 2 := by
    have := Nat.le_of_dvd (by decide) hd
    omega
  apply no_period_two_of_Q01 hQ
  refine ⟨T, fun t ht => ?_⟩
  rcases hP12 with rfl | rfl
  · rw [show t + 2 = (t + 1) + 1 from rfl, hper (t + 1) (by omega), hper t ht]
  · exact hper t ht

/-- In `EventuallyPeriodic` form: Q01 excludes eventual period 1 and 2. -/
theorem not_ep12_of_Q01 (hQ : Q01) :
    ¬ ∃ T P, (P = 1 ∨ P = 2) ∧ ∀ t, T ≤ t → center (t + P) = center t := by
  rintro ⟨T, P, hP, h⟩
  exact no_period_dvd_two_of_Q01 hQ T P (by omega) (by rcases hP with rfl | rfl <;> decide) h

/-- Sanity: the ZBL identity really is about the true pattern at negative positions (Int form). -/
theorem cell_eq_zrow_int {T : Nat} (h : ∀ t, T ≤ t → (center t && center (t + 1)) = false)
    (t : Nat) (p : Int) (hp : p ≤ -1) :
    cell (T + t) p = zrow (fun k => cell T (-(k : Int))) t p.natAbs := by
  obtain ⟨k, hk⟩ : ∃ k : Nat, p = -((k + 1 : Nat) : Int) := ⟨p.natAbs - 1, by omega⟩
  subst hk
  rw [cell_eq_zrow h t k]
  congr 1

end R30ZBLCheck

#print axioms R30ZBL.no_period_two_of_Q01
#print axioms R30ZBL.cell_eq_zrow
#print axioms R30ZBLCheck.no_period_dvd_two_of_Q01
#print axioms R30ZBLCheck.not_ep12_of_Q01
#print axioms R30ZBLCheck.cell_eq_zrow_int
#print axioms Ruliology.CellularAutomata.Rule30Prize.center_not_eventually_constant
#print axioms R30ZBL.Q01_iff_Phi
