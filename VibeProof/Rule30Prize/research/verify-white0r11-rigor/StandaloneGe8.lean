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
# Rule 30: the words `0^r 1 1` (`r ≥ 10`) are absorbing on the right

If the center column is eventually periodic with repeating word `0^r 1 1`, `r ≥ 10`, then column 1
is eventually periodic, which contradicts Jen's theorem.

* `cell_eq_false_of_gt`, `cell_right_edge`: the right edge of the pattern.
* `nine_black`: Lemma A (copied from `AbsorbRight.lean`): nine consecutive black cells in a column
  force a white cell in the next column right after them.
* `front_moves`: during a white run of the center column, the leftmost black cell of the right half
  moves left by one column per step.
* `black_stays`: during a white run, a black cell in column 1 stays black.
* One period of `0^r 1 1`, by the position `ℓ` of the first black cell at its start:
  `ℓ ≤ r - 8` locks (`period_lock`); the other cases put the first black cell at column `≤ 3`
  at the start of the next period, except `ℓ = r + 2`, where column 1 reads `0^{r+1} 1`.
-/

namespace AbsorbWhite

open Ruliology.CellularAutomata.Rule30Jen
open Ruliology.CellularAutomata.Rule30Prize

/-! ### Lemma A (same proof as in `AbsorbRight.lean`) -/

def rowAt (t : Nat) (p : Int) : Nat → List Bool
  | 0 => []
  | n + 1 => cell t p :: rowAt t (p + 1) n

theorem length_rowAt (t : Nat) : ∀ (n : Nat) (p : Int), (rowAt t p n).length = n
  | 0, _ => rfl
  | n + 1, p => by simp [rowAt, length_rowAt t n (p + 1)]

def stepRow (l : Bool) : List Bool → List Bool
  | a :: b :: rest => rule l a b :: stepRow a (b :: rest)
  | _ => []

theorem stepRow_rowAt (t : Nat) : ∀ (n : Nat) (p : Int),
    stepRow (cell t (p - 1)) (rowAt t p (n + 1)) = rowAt (t + 1) p n
  | 0, _ => rfl
  | n + 1, p => by
    have ih := stepRow_rowAt t n (p + 1)
    rw [show p + 1 - 1 = p by omega] at ih
    show rule (cell t (p - 1)) (cell t p) (cell t (p + 1)) ::
        stepRow (cell t p) (rowAt t (p + 1) (n + 1)) = cell (t + 1) p :: rowAt (t + 1) (p + 1) n
    rw [ih]
    rfl

def runBlack : Nat → List Bool → List Bool
  | 0, L => L
  | k + 1, L => runBlack k (stepRow true L)

theorem runBlack_rowAt (m : Int) : ∀ (k n t : Nat), (∀ s, s < k → cell (t + s) m = true) →
    runBlack k (rowAt t (m + 1) (n + k)) = rowAt (t + k) (m + 1) n
  | 0, n, t, _ => by simp [runBlack]
  | k + 1, n, t, h => by
    have h0 : cell t m = true := by simpa using h 0 (by omega)
    have hstep : stepRow true (rowAt t (m + 1) (n + k + 1)) = rowAt (t + 1) (m + 1) (n + k) := by
      have := stepRow_rowAt t (n + k) (m + 1)
      rw [show m + 1 - 1 = m by omega, h0] at this
      exact this
    have ih := runBlack_rowAt m k n (t + 1) (fun s hs => by
      have := h (s + 1) (by omega)
      rwa [show t + (s + 1) = t + 1 + s by omega] at this)
    show runBlack k (stepRow true (rowAt t (m + 1) (n + (k + 1)))) = rowAt (t + (k + 1)) (m + 1) n
    rw [show n + (k + 1) = n + k + 1 by omega, hstep, ih, show t + 1 + k = t + (k + 1) by omega]

theorem nine_black_core : ∀ L ∈ allLists 11, runBlack 9 L = [false, true] := by
  decide +kernel

theorem nine_black (t : Nat) (m : Int) (h : ∀ s, s < 9 → cell (t + s) m = true) :
    cell (t + 9) (m + 1) = false ∧ cell (t + 9) (m + 2) = true := by
  have h1 := runBlack_rowAt m 9 2 t h
  have hmem : rowAt t (m + 1) (2 + 9) ∈ allLists 11 := by
    have := mem_allLists (rowAt t (m + 1) (2 + 9))
    rwa [length_rowAt] at this
  rw [nine_black_core _ hmem] at h1
  have h2 : rowAt (t + 9) (m + 1) 2 = [cell (t + 9) (m + 1), cell (t + 9) (m + 1 + 1)] := rfl
  rw [h2] at h1
  simp only [List.cons.injEq] at h1
  refine ⟨h1.1.symm, ?_⟩
  rw [show m + 2 = m + 1 + 1 by omega]
  exact h1.2.1.symm

/-! ### The right edge -/

theorem cell_eq_false_of_gt : ∀ (t : Nat) (p : Int), (t : Int) < p → cell t p = false
  | 0, p, h => by simp [cell]; omega
  | t + 1, p, h => by
    show rule (cell t (p - 1)) (cell t p) (cell t (p + 1)) = false
    rw [cell_eq_false_of_gt t (p - 1) (by omega), cell_eq_false_of_gt t p (by omega),
      cell_eq_false_of_gt t (p + 1) (by omega)]
    rfl

theorem cell_right_edge : ∀ t : Nat, cell t (t : Int) = true
  | 0 => rfl
  | t + 1 => by
    show rule (cell t (((t + 1 : Nat) : Int) - 1)) (cell t ((t + 1 : Nat) : Int))
      (cell t (((t + 1 : Nat) : Int) + 1)) = true
    rw [show ((t + 1 : Nat) : Int) - 1 = (t : Int) by omega, cell_right_edge t,
      cell_eq_false_of_gt t _ (by omega), cell_eq_false_of_gt t _ (by omega)]
    rfl

/-- The first black cell to the right of the center exists at every time `t ≥ 1`. -/
theorem first_black_aux (t : Nat) : ∀ n : Nat, (∀ p : Nat, 1 ≤ p → p ≤ n → cell t p = false) ∨
    ∃ ℓ, ℓ < n ∧ (∀ p : Nat, 1 ≤ p → p ≤ ℓ → cell t p = false) ∧ cell t ((ℓ + 1 : Nat) : Int) = true
  | 0 => Or.inl (fun p h1 h2 => by omega)
  | n + 1 => by
    rcases first_black_aux t n with hw | ⟨ℓ, hℓ, hw, hb⟩
    · by_cases hc : cell t ((n + 1 : Nat) : Int) = true
      · exact Or.inr ⟨n, by omega, hw, hc⟩
      · refine Or.inl (fun p h1 h2 => ?_)
        by_cases hp : p ≤ n
        · exact hw p h1 hp
        · have : p = n + 1 := by omega
          subst this
          simpa using hc
    · exact Or.inr ⟨ℓ, by omega, hw, hb⟩

theorem first_black (t : Nat) (ht : 1 ≤ t) :
    ∃ ℓ, (∀ p : Nat, 1 ≤ p → p ≤ ℓ → cell t p = false) ∧ cell t ((ℓ + 1 : Nat) : Int) = true := by
  rcases first_black_aux t t with hw | ⟨ℓ, _, hw, hb⟩
  · have := hw t ht (Nat.le_refl t)
    rw [cell_right_edge] at this
    exact absurd this (by decide)
  · exact ⟨ℓ, hw, hb⟩

/-! ### White runs of the center column -/

/-- During a white run, the first black cell moves one column to the left per step. -/
theorem front_moves (a ℓ n : Nat) (hc : ∀ i, i < n → cell (a + i) 0 = false)
    (hw : ∀ p : Nat, 1 ≤ p → p ≤ ℓ → cell a p = false) (hb : cell a ((ℓ + 1 : Nat) : Int) = true) :
    ∀ i, i ≤ n → i ≤ ℓ →
      (∀ p : Nat, 1 ≤ p → p ≤ ℓ - i → cell (a + i) p = false) ∧
        cell (a + i) ((ℓ - i + 1 : Nat) : Int) = true
  | 0, _, _ => ⟨fun p h1 h2 => by simpa using hw p h1 (by omega), by simpa using hb⟩
  | i + 1, hin, hil => by
    obtain ⟨ihw, ihb⟩ := front_moves a ℓ n hc hw hb i (by omega) (by omega)
    -- white in columns 0..ℓ-i at time a+i (column 0: the center)
    have wh : ∀ q : Int, 0 ≤ q → q ≤ ((ℓ - i : Nat) : Int) → cell (a + i) q = false := by
      intro q hq0 hq1
      by_cases hq : q = 0
      · subst hq; exact hc i (by omega)
      · have := ihw q.toNat (by omega) (by omega)
        rwa [show ((q.toNat : Nat) : Int) = q by omega] at this
    refine ⟨fun p h1 h2 => ?_, ?_⟩
    · show rule (cell (a + i) ((p : Int) - 1)) (cell (a + i) (p : Int)) (cell (a + i) ((p : Int) + 1)) = false
      rw [wh _ (by omega) (by omega), wh _ (by omega) (by omega), wh _ (by omega) (by omega)]
      rfl
    · show rule (cell (a + i) (((ℓ - (i + 1) + 1 : Nat) : Int) - 1))
        (cell (a + i) ((ℓ - (i + 1) + 1 : Nat) : Int)) (cell (a + i) (((ℓ - (i + 1) + 1 : Nat) : Int) + 1)) = true
      rw [wh _ (by omega) (by omega), wh _ (by omega) (by omega),
        show ((ℓ - (i + 1) + 1 : Nat) : Int) + 1 = ((ℓ - i + 1 : Nat) : Int) by omega, ihb]
      rfl

/-- During a white run, a black cell in column 1 stays black. -/
theorem black_stays (a n : Nat) (hc : ∀ i, i < n → cell (a + i) 0 = false) (h1 : cell a 1 = true) :
    ∀ i, i ≤ n → cell (a + i) 1 = true
  | 0, _ => by simpa using h1
  | i + 1, hi => by
    have ih := black_stays a n hc h1 i (by omega)
    show rule (cell (a + i) (1 - 1)) (cell (a + i) 1) (cell (a + i) (1 + 1)) = true
    rw [show (1 : Int) - 1 = 0 by rfl, hc i (by omega), ih]
    rfl

/-! ### One period of `0^r 1 1` -/

section Period
variable (a r : Nat)
  (hwr : ∀ i, i < r → cell (a + i) 0 = false)
  (hb1 : cell (a + r) 0 = true) (hb2 : cell (a + r + 1) 0 = true)
include hwr hb1 hb2

/-- First black cell at column `ℓ + 1 ≤ r - 7`: next period starts with a black cell in column 1. -/
theorem period_lock (hr : 8 ≤ r) (ℓ : Nat) (hℓ : ℓ ≤ r - 8)
    (hw : ∀ p : Nat, 1 ≤ p → p ≤ ℓ → cell a p = false) (hb : cell a ((ℓ + 1 : Nat) : Int) = true) :
    (∀ i, ℓ ≤ i → i ≤ r → cell (a + i) 1 = true) ∧ cell (a + r + 1) 1 = false ∧
      cell (a + r + 2) 1 = true := by
  have hfront := (front_moves a ℓ r hwr hw hb ℓ (by omega) (Nat.le_refl ℓ)).2
  rw [show ℓ - ℓ + 1 = 1 by omega] at hfront
  have hblk : ∀ i, ℓ ≤ i → i ≤ r → cell (a + i) 1 = true := by
    intro i h1 h2
    have := black_stays (a + ℓ) (r - ℓ) (fun j hj => by
      have := hwr (ℓ + j) (by omega); rwa [show a + (ℓ + j) = a + ℓ + j by omega] at this)
      (by simpa using hfront) (i - ℓ) (by omega)
    rwa [show a + ℓ + (i - ℓ) = a + i by omega] at this
  have hA := (nine_black (a + (r - 8)) 1 (fun s hs => by
    have := hblk (r - 8 + s) (by omega) (by omega)
    rwa [show a + (r - 8 + s) = a + (r - 8) + s by omega] at this)).1
  rw [show a + (r - 8) + 9 = a + r + 1 by omega, show (1 : Int) + 1 = 2 by rfl] at hA
  have c1 : cell (a + r + 1) 1 = false := by
    show rule (cell (a + r) (1 - 1)) (cell (a + r) 1) (cell (a + r) (1 + 1)) = false
    rw [show (1 : Int) - 1 = 0 by rfl, hb1, hblk r (by omega) (Nat.le_refl r)]
    rfl
  refine ⟨hblk, c1, ?_⟩
  show rule (cell (a + r + 1) (1 - 1)) (cell (a + r + 1) 1) (cell (a + r + 1) (1 + 1)) = true
  rw [show (1 : Int) - 1 = 0 by rfl, show (1 : Int) + 1 = 2 by rfl, hb2, c1, hA]
  rfl

/-- First black cell at column `ℓ + 1 ∈ [r - 6, r + 1]`: the next period's first black cell is in
column 1 or 2. -/
theorem period_late (ℓ : Nat) (hℓ : ℓ ≤ r)
    (hw : ∀ p : Nat, 1 ≤ p → p ≤ ℓ → cell a p = false) (hb : cell a ((ℓ + 1 : Nat) : Int) = true) :
    cell (a + r + 2) 1 = true ∨ (cell (a + r + 2) 1 = false ∧ cell (a + r + 2) 2 = true) := by
  have hfront := (front_moves a ℓ r hwr hw hb ℓ (by omega) (Nat.le_refl ℓ)).2
  rw [show ℓ - ℓ + 1 = 1 by omega] at hfront
  have hr1 : cell (a + r) 1 = true := by
    have := black_stays (a + ℓ) (r - ℓ) (fun j hj => by
      have := hwr (ℓ + j) (by omega); rwa [show a + (ℓ + j) = a + ℓ + j by omega] at this)
      (by simpa using hfront) (r - ℓ) (Nat.le_refl _)
    rwa [show a + ℓ + (r - ℓ) = a + r by omega] at this
  have c1 : cell (a + r + 1) 1 = false := by
    show rule (cell (a + r) (1 - 1)) (cell (a + r) 1) (cell (a + r) (1 + 1)) = false
    rw [show (1 : Int) - 1 = 0 by rfl, hb1, hr1]
    rfl
  cases h2 : cell (a + r + 1) 2
  · left
    show rule (cell (a + r + 1) (1 - 1)) (cell (a + r + 1) 1) (cell (a + r + 1) (1 + 1)) = true
    rw [show (1 : Int) - 1 = 0 by rfl, show (1 : Int) + 1 = 2 by rfl, hb2, c1, h2]
    rfl
  · right
    constructor
    · show rule (cell (a + r + 1) (1 - 1)) (cell (a + r + 1) 1) (cell (a + r + 1) (1 + 1)) = false
      rw [show (1 : Int) - 1 = 0 by rfl, show (1 : Int) + 1 = 2 by rfl, hb2, c1, h2]
      rfl
    · show rule (cell (a + r + 1) (2 - 1)) (cell (a + r + 1) 2) (cell (a + r + 1) (2 + 1)) = true
      rw [show (2 : Int) - 1 = 1 by rfl, c1, h2]
      rfl

omit hb1 hb2 in
/-- The configuration at time `a + r` when the first black cell started at column `r + z + 1`. -/
theorem period_far (z : Nat) (hz : 1 ≤ z)
    (hw : ∀ p : Nat, 1 ≤ p → p ≤ r + z → cell a p = false) (hb : cell a ((r + z + 1 : Nat) : Int) = true) :
    (∀ p : Nat, 1 ≤ p → p ≤ z → cell (a + r) p = false) ∧ cell (a + r) ((z + 1 : Nat) : Int) = true := by
  have := front_moves a (r + z) r hwr hw hb r (Nat.le_refl r) (by omega)
  rw [show r + z - r = z by omega] at this
  exact this

theorem period_z1 (hw : ∀ p : Nat, 1 ≤ p → p ≤ r + 1 → cell a p = false)
    (hb : cell a ((r + 1 + 1 : Nat) : Int) = true) :
    cell (a + r + 2) 1 = false ∧ cell (a + r + 2) 2 = true := by
  obtain ⟨fw, fb⟩ := period_far a r hwr 1 (Nat.le_refl 1) hw hb
  have w1 : cell (a + r) 1 = false := by simpa using fw 1 (Nat.le_refl 1) (Nat.le_refl 1)
  have b2 : cell (a + r) 2 = true := by simpa using fb
  have c1 : cell (a + r + 1) 1 = false := by
    show rule (cell (a + r) (1 - 1)) (cell (a + r) 1) (cell (a + r) (1 + 1)) = false
    rw [show (1 : Int) - 1 = 0 by rfl, show (1 : Int) + 1 = 2 by rfl, hb1, w1, b2]; rfl
  have c2 : cell (a + r + 1) 2 = true := by
    show rule (cell (a + r) (2 - 1)) (cell (a + r) 2) (cell (a + r) (2 + 1)) = true
    rw [show (2 : Int) - 1 = 1 by rfl, w1, b2]; rfl
  constructor
  · show rule (cell (a + r + 1) (1 - 1)) (cell (a + r + 1) 1) (cell (a + r + 1) (1 + 1)) = false
    rw [show (1 : Int) - 1 = 0 by rfl, show (1 : Int) + 1 = 2 by rfl, hb2, c1, c2]; rfl
  · show rule (cell (a + r + 1) (2 - 1)) (cell (a + r + 1) 2) (cell (a + r + 1) (2 + 1)) = true
    rw [show (2 : Int) - 1 = 1 by rfl, c1, c2]; rfl

omit hb2 in
theorem period_z2 (hw : ∀ p : Nat, 1 ≤ p → p ≤ r + 2 → cell a p = false)
    (hb : cell a ((r + 2 + 1 : Nat) : Int) = true) :
    (∀ i, i ≤ r → cell (a + i) 1 = false) ∧ cell (a + r + 1) 1 = true := by
  have hw' : ∀ p : Nat, 1 ≤ p → p ≤ r + 2 → cell a p = false := hw
  refine ⟨fun i hi => ?_, ?_⟩
  · have := (front_moves a (r + 2) r hwr hw hb i hi (by omega)).1 1 (Nat.le_refl 1) (by omega)
    simpa using this
  · obtain ⟨fw, _⟩ := period_far a r hwr 2 (by omega) hw hb
    have w1 : cell (a + r) 1 = false := by simpa using fw 1 (by omega) (by omega)
    have w2 : cell (a + r) 2 = false := by simpa using fw 2 (by omega) (by omega)
    show rule (cell (a + r) (1 - 1)) (cell (a + r) 1) (cell (a + r) (1 + 1)) = true
    rw [show (1 : Int) - 1 = 0 by rfl, show (1 : Int) + 1 = 2 by rfl, hb1, w1, w2]; rfl

theorem period_z3 (hw : ∀ p : Nat, 1 ≤ p → p ≤ r + 3 → cell a p = false)
    (hb : cell a ((r + 3 + 1 : Nat) : Int) = true) :
    cell (a + r + 2) 1 = false ∧ cell (a + r + 2) 2 = false ∧ cell (a + r + 2) 3 = true := by
  obtain ⟨fw, fb⟩ := period_far a r hwr 3 (by omega) hw hb
  have w1 : cell (a + r) 1 = false := by simpa using fw 1 (by omega) (by omega)
  have w2 : cell (a + r) 2 = false := by simpa using fw 2 (by omega) (by omega)
  have w3 : cell (a + r) 3 = false := by simpa using fw 3 (by omega) (by omega)
  have b4 : cell (a + r) 4 = true := by simpa using fb
  have c1 : cell (a + r + 1) 1 = true := by
    show rule (cell (a + r) (1 - 1)) (cell (a + r) 1) (cell (a + r) (1 + 1)) = true
    rw [show (1 : Int) - 1 = 0 by rfl, show (1 : Int) + 1 = 2 by rfl, hb1, w1, w2]; rfl
  have c2 : cell (a + r + 1) 2 = false := by
    show rule (cell (a + r) (2 - 1)) (cell (a + r) 2) (cell (a + r) (2 + 1)) = false
    rw [show (2 : Int) - 1 = 1 by rfl, show (2 : Int) + 1 = 3 by rfl, w1, w2, w3]; rfl
  have c3 : cell (a + r + 1) 3 = true := by
    show rule (cell (a + r) (3 - 1)) (cell (a + r) 3) (cell (a + r) (3 + 1)) = true
    rw [show (3 : Int) - 1 = 2 by rfl, show (3 : Int) + 1 = 4 by rfl, w2, w3, b4]; rfl
  refine ⟨?_, ?_, ?_⟩
  · show rule (cell (a + r + 1) (1 - 1)) (cell (a + r + 1) 1) (cell (a + r + 1) (1 + 1)) = false
    rw [show (1 : Int) - 1 = 0 by rfl, show (1 : Int) + 1 = 2 by rfl, hb2, c1, c2]; rfl
  · show rule (cell (a + r + 1) (2 - 1)) (cell (a + r + 1) 2) (cell (a + r + 1) (2 + 1)) = false
    rw [show (2 : Int) - 1 = 1 by rfl, show (2 : Int) + 1 = 3 by rfl, c1, c2, c3]; rfl
  · show rule (cell (a + r + 1) (3 - 1)) (cell (a + r + 1) 3) (cell (a + r + 1) (3 + 1)) = true
    rw [show (3 : Int) - 1 = 2 by rfl, c2, c3]; rfl

theorem period_z4 (z : Nat) (hz : 4 ≤ z) (hw : ∀ p : Nat, 1 ≤ p → p ≤ r + z → cell a p = false)
    (hb : cell a ((r + z + 1 : Nat) : Int) = true) :
    cell (a + r + 2) 1 = false ∧ cell (a + r + 2) 2 = true := by
  obtain ⟨fw, _⟩ := period_far a r hwr z (by omega) hw hb
  have w1 : cell (a + r) 1 = false := by simpa using fw 1 (by omega) (by omega)
  have w2 : cell (a + r) 2 = false := by simpa using fw 2 (by omega) (by omega)
  have w3 : cell (a + r) 3 = false := by simpa using fw 3 (by omega) (by omega)
  have w4 : cell (a + r) 4 = false := by simpa using fw 4 (by omega) (by omega)
  have c1 : cell (a + r + 1) 1 = true := by
    show rule (cell (a + r) (1 - 1)) (cell (a + r) 1) (cell (a + r) (1 + 1)) = true
    rw [show (1 : Int) - 1 = 0 by rfl, show (1 : Int) + 1 = 2 by rfl, hb1, w1, w2]; rfl
  have c2 : cell (a + r + 1) 2 = false := by
    show rule (cell (a + r) (2 - 1)) (cell (a + r) 2) (cell (a + r) (2 + 1)) = false
    rw [show (2 : Int) - 1 = 1 by rfl, show (2 : Int) + 1 = 3 by rfl, w1, w2, w3]; rfl
  have c3 : cell (a + r + 1) 3 = false := by
    show rule (cell (a + r) (3 - 1)) (cell (a + r) 3) (cell (a + r) (3 + 1)) = false
    rw [show (3 : Int) - 1 = 2 by rfl, show (3 : Int) + 1 = 4 by rfl, w2, w3, w4]; rfl
  constructor
  · show rule (cell (a + r + 1) (1 - 1)) (cell (a + r + 1) 1) (cell (a + r + 1) (1 + 1)) = false
    rw [show (1 : Int) - 1 = 0 by rfl, show (1 : Int) + 1 = 2 by rfl, hb2, c1, c2]; rfl
  · show rule (cell (a + r + 1) (2 - 1)) (cell (a + r + 1) 2) (cell (a + r + 1) (2 + 1)) = true
    rw [show (2 : Int) - 1 = 1 by rfl, show (2 : Int) + 1 = 3 by rfl, c1, c2, c3]; rfl

end Period

/-! ### Assembly -/

/-- Column 1 is eventually periodic if it repeats a fixed block from some time on. -/
theorem periodic_blocks (B Q : Nat) (hQ : 0 < Q) (g : Nat → Bool)
    (h : ∀ j i, i < Q → cell (B + j * Q + i) 1 = g i) :
    EventuallyPeriodic (fun t => cell t (0 + 1)) := by
  refine ⟨B, Q, hQ, fun t ht => ?_⟩
  show cell (t + Q) (0 + 1) = cell t (0 + 1)
  rw [show (0 : Int) + 1 = 1 by rfl]
  have hdm := Nat.div_add_mod (t - B) Q
  generalize (t - B) / Q = q at hdm
  have hmod := Nat.mod_lt (t - B) hQ
  generalize (t - B) % Q = s at hdm hmod
  have hq1 : (q + 1) * Q = q * Q + Q := Nat.succ_mul q Q
  have hcomm : Q * q = q * Q := Nat.mul_comm Q q
  have e1 := h q s hmod
  have e2 := h (q + 1) s hmod
  rw [hq1] at e2
  rw [show t + Q = B + (q * Q + Q) + s by omega, e2, ← e1, show B + q * Q + s = t by omega]

/-- **The words `0^r 1 1`, `r ≥ 10`, are excluded**: the center column of rule 30 is not
eventually periodic with repeating word `0^r 1 1`, whatever the transient. -/
theorem no_white_run_11 (T r t0 : Nat) (hr : 10 ≤ r)
    (hper : ∀ t, T ≤ t → center (t + (r + 2)) = center t) (ht0 : T ≤ t0)
    (hw : ∀ i, i < r → center (t0 + i) = false) (hb1 : center (t0 + r) = true)
    (hb2 : center (t0 + r + 1) = true) : False := by
  generalize hQdef : r + 2 = Q at hper
  have hQ : 0 < Q := by omega
  have hperk : ∀ k t, T ≤ t → center (t + k * Q) = center t := periodic_mul hper
  -- start one period later so that the start time is ≥ 1
  generalize hAdef : t0 + Q = A
  have hMul : ∀ k, (k + 1) * Q = k * Q + Q := fun k => Nat.succ_mul k Q
  have drvw : ∀ k i, i < r → cell (A + k * Q + i) 0 = false := by
    intro k i hi
    have := hperk (k + 1) (t0 + i) (by omega)
    show center (A + k * Q + i) = false
    rw [hMul k, show t0 + i + (k * Q + Q) = A + k * Q + i by omega] at this
    rw [this]; exact hw i hi
  have drvb1 : ∀ k, cell (A + k * Q + r) 0 = true := by
    intro k
    have := hperk (k + 1) (t0 + r) (by omega)
    show center (A + k * Q + r) = true
    rw [hMul k, show t0 + r + (k * Q + Q) = A + k * Q + r by omega] at this
    rw [this]; exact hb1
  have drvb2 : ∀ k, cell (A + k * Q + r + 1) 0 = true := by
    intro k
    have := hperk (k + 1) (t0 + r + 1) (by omega)
    show center (A + k * Q + r + 1) = true
    rw [hMul k, show t0 + r + 1 + (k * Q + Q) = A + k * Q + r + 1 by omega] at this
    rw [this]; exact hb2
  have hnext : ∀ k, A + k * Q + r + 2 = A + (k + 1) * Q := by intro k; rw [hMul k]; omega
  -- a first black cell at column ℓ + 1 ≤ r - 7 locks the next period
  have early : ∀ k ℓ, ℓ ≤ r - 8 → (∀ p : Nat, 1 ≤ p → p ≤ ℓ → cell (A + k * Q) p = false) →
      cell (A + k * Q) ((ℓ + 1 : Nat) : Int) = true → cell (A + (k + 1) * Q) 1 = true := by
    intro k ℓ hℓ hwℓ hbℓ
    have := (period_lock (A + k * Q) r (drvw k) (drvb1 k) (drvb2 k) (by omega) ℓ hℓ hwℓ hbℓ).2.2
    rwa [hnext k] at this
  have lock_step : ∀ k, cell (A + k * Q) 1 = true → cell (A + (k + 1) * Q) 1 = true := by
    intro k hk
    exact early k 0 (by omega) (fun p h1 h2 => by omega) (by simpa using hk)
  have lock_all : ∀ k, cell (A + k * Q) 1 = true → ∀ j, cell (A + (k + j) * Q) 1 = true := by
    intro k hk j
    induction j with
    | zero => simpa using hk
    | succ j ih => rw [show k + (j + 1) = (k + j) + 1 by omega]; exact lock_step _ ih
  -- the exceptional case: first black cell exactly at column r + 3
  let Z2 : Nat → Prop := fun k => (∀ p : Nat, 1 ≤ p → p ≤ r + 2 → cell (A + k * Q) p = false) ∧
    cell (A + k * Q) ((r + 2 + 1 : Nat) : Int) = true
  have two_lock : ∀ k, ¬ Z2 k → cell (A + (k + 2) * Q) 1 = true := by
    intro k hz
    have hA1 : 1 ≤ A + k * Q := by omega
    obtain ⟨ℓ, hwℓ, hbℓ⟩ := first_black (A + k * Q) hA1
    have via1 : cell (A + (k + 1) * Q) 1 = false → cell (A + (k + 1) * Q) 2 = true →
        cell (A + (k + 2) * Q) 1 = true := by
      intro h1 h2
      have := early (k + 1) 1 (by omega) (fun p hp1 hp2 => by
        have : p = 1 := by omega
        subst this; simpa using h1) (by simpa using h2)
      rwa [show k + 1 + 1 = k + 2 by omega] at this
    by_cases c1 : ℓ ≤ r - 8
    · have := lock_step _ (early k ℓ c1 hwℓ hbℓ)
      rwa [show k + 1 + 1 = k + 2 by omega] at this
    by_cases c2 : ℓ ≤ r
    · rcases period_late (A + k * Q) r (drvw k) (drvb1 k) (drvb2 k) ℓ c2 hwℓ hbℓ with h | ⟨h1, h2⟩
      · rw [hnext k] at h
        have := lock_step _ h
        rwa [show k + 1 + 1 = k + 2 by omega] at this
      · rw [hnext k] at h1 h2
        exact via1 h1 h2
    by_cases c3 : ℓ = r + 1
    · subst c3
      obtain ⟨h1, h2⟩ := period_z1 (A + k * Q) r (drvw k) (drvb1 k) (drvb2 k) hwℓ hbℓ
      rw [hnext k] at h1 h2
      exact via1 h1 h2
    by_cases c4 : ℓ = r + 2
    · subst c4
      exact absurd ⟨hwℓ, hbℓ⟩ hz
    by_cases c5 : ℓ = r + 3
    · subst c5
      obtain ⟨h1, h2, h3⟩ := period_z3 (A + k * Q) r (drvw k) (drvb1 k) (drvb2 k) hwℓ hbℓ
      rw [hnext k] at h1 h2 h3
      have := early (k + 1) 2 (by omega) (fun p hp1 hp2 => by
        by_cases hp : p = 1
        · subst hp; simpa using h1
        · have : p = 2 := by omega
          subst this; simpa using h2) (by simpa using h3)
      rwa [show k + 1 + 1 = k + 2 by omega] at this
    · have hz4 : 4 ≤ ℓ - r := by omega
      obtain ⟨h1, h2⟩ := period_z4 (A + k * Q) r (drvw k) (drvb1 k) (drvb2 k) (ℓ - r) hz4
        (fun p hp1 hp2 => hwℓ p hp1 (by omega)) (by rw [show r + (ℓ - r) + 1 = ℓ + 1 by omega]; exact hbℓ)
      rw [hnext k] at h1 h2
      exact via1 h1 h2
  -- column 1 over one period, in the lock and in the exceptional case
  have lock_pattern : ∀ k, cell (A + k * Q) 1 = true → ∀ i, i < Q →
      cell (A + k * Q + i) 1 = decide (i ≤ r) := by
    intro k hk i hi
    obtain ⟨hblk, c1, _⟩ := period_lock (A + k * Q) r (drvw k) (drvb1 k) (drvb2 k) (by omega) 0
      (by omega) (fun p h1 h2 => by omega) (by simpa using hk)
    by_cases hir : i ≤ r
    · rw [hblk i (by omega) hir]; simp [hir]
    · have : i = r + 1 := by omega
      subst this; rw [show A + k * Q + (r + 1) = A + k * Q + r + 1 by omega, c1]; simp
  have z2_pattern : ∀ k, Z2 k → ∀ i, i < Q → cell (A + k * Q + i) 1 = decide (i = r + 1) := by
    intro k hk i hi
    obtain ⟨hw0, c1⟩ := period_z2 (A + k * Q) r (drvw k) (drvb1 k) hk.1 hk.2
    by_cases hir : i ≤ r
    · rw [hw0 i hir]; simp; omega
    · have : i = r + 1 := by omega
      subst this; rw [show A + k * Q + (r + 1) = A + k * Q + r + 1 by omega, c1]; simp
  have h1 : EventuallyPeriodic (fun t => cell t (0 + 1)) := by
    by_cases hall : ∀ k, Z2 k
    · exact periodic_blocks A Q hQ (fun i => decide (i = r + 1)) (fun j i hi => z2_pattern j (hall j) i hi)
    · have hex : ∃ k, ¬ Z2 k := Classical.byContradiction fun hne => hall fun k =>
        Classical.byContradiction fun hk => hne ⟨k, hk⟩
      obtain ⟨k, hk⟩ := hex
      have hlock := two_lock k hk
      refine periodic_blocks (A + (k + 2) * Q) Q hQ (fun i => decide (i ≤ r)) (fun j i hi => ?_)
      have := lock_pattern (k + 2 + j) (lock_all (k + 2) hlock j) i hi
      have hm : (k + 2 + j) * Q = (k + 2) * Q + j * Q := Nat.add_mul (k + 2) j Q
      rwa [hm, show A + ((k + 2) * Q + j * Q) + i = A + (k + 2) * Q + j * Q + i by omega] at this
  have h0 : EventuallyPeriodic (fun t => cell t 0) := ⟨T, Q, hQ, hper⟩
  exact not_adjacent 0 h0 h1

end AbsorbWhite

/-! ### Verifier's extension: the same lemmas give the exclusion for every `r ≥ 8` -/

namespace AbsorbWhiteGe8

open Ruliology.CellularAutomata.Rule30Jen
open Ruliology.CellularAutomata.Rule30Prize
open AbsorbWhite

theorem no_white_run_11_ge8 (T r t0 : Nat) (hr : 8 ≤ r)
    (hper : ∀ t, T ≤ t → center (t + (r + 2)) = center t) (ht0 : T ≤ t0)
    (hw : ∀ i, i < r → center (t0 + i) = false) (hb1 : center (t0 + r) = true)
    (hb2 : center (t0 + r + 1) = true) : False := by
  generalize hQdef : r + 2 = Q at hper
  have hQ : 0 < Q := by omega
  have hperk : ∀ k t, T ≤ t → center (t + k * Q) = center t := periodic_mul hper
  generalize hAdef : t0 + Q = A
  have hMul : ∀ k, (k + 1) * Q = k * Q + Q := fun k => Nat.succ_mul k Q
  have drvw : ∀ k i, i < r → cell (A + k * Q + i) 0 = false := by
    intro k i hi
    have := hperk (k + 1) (t0 + i) (by omega)
    show center (A + k * Q + i) = false
    rw [hMul k, show t0 + i + (k * Q + Q) = A + k * Q + i by omega] at this
    rw [this]; exact hw i hi
  have drvb1 : ∀ k, cell (A + k * Q + r) 0 = true := by
    intro k
    have := hperk (k + 1) (t0 + r) (by omega)
    show center (A + k * Q + r) = true
    rw [hMul k, show t0 + r + (k * Q + Q) = A + k * Q + r by omega] at this
    rw [this]; exact hb1
  have drvb2 : ∀ k, cell (A + k * Q + r + 1) 0 = true := by
    intro k
    have := hperk (k + 1) (t0 + r + 1) (by omega)
    show center (A + k * Q + r + 1) = true
    rw [hMul k, show t0 + r + 1 + (k * Q + Q) = A + k * Q + r + 1 by omega] at this
    rw [this]; exact hb2
  have hnext : ∀ k, A + k * Q + r + 2 = A + (k + 1) * Q := by intro k; rw [hMul k]; omega
  -- S0 k : column 1 black at the start of period k (class 0); it is absorbing for r ≥ 8
  have s0_step : ∀ k, cell (A + k * Q) 1 = true → cell (A + (k + 1) * Q) 1 = true := by
    intro k hk
    have := (period_lock (A + k * Q) r (drvw k) (drvb1 k) (drvb2 k) hr 0 (by omega)
      (fun p h1 h2 => by omega) (by simpa using hk)).2.2
    rwa [hnext k] at this
  -- first black cell at column ℓ+1 with ℓ ≤ r: next period is in class 0 or class 1
  have late : ∀ k ℓ, ℓ ≤ r → (∀ p : Nat, 1 ≤ p → p ≤ ℓ → cell (A + k * Q) p = false) →
      cell (A + k * Q) ((ℓ + 1 : Nat) : Int) = true →
      cell (A + (k + 1) * Q) 1 = true ∨
        (cell (A + (k + 1) * Q) 1 = false ∧ cell (A + (k + 1) * Q) 2 = true) := by
    intro k ℓ hℓ hwℓ hbℓ
    have := period_late (A + k * Q) r (drvw k) (drvb1 k) (drvb2 k) ℓ hℓ hwℓ hbℓ
    rwa [hnext k] at this
  have s1_step : ∀ k, (cell (A + k * Q) 1 = false ∧ cell (A + k * Q) 2 = true) →
      cell (A + (k + 1) * Q) 1 = true ∨
        (cell (A + (k + 1) * Q) 1 = false ∧ cell (A + (k + 1) * Q) 2 = true) := by
    intro k hk
    exact late k 1 (by omega) (fun p hp1 hp2 => by
      have : p = 1 := by omega
      subst this; simpa using hk.1) (by simpa using hk.2)
  have step01 : ∀ k, (cell (A + k * Q) 1 = true ∨
        (cell (A + k * Q) 1 = false ∧ cell (A + k * Q) 2 = true)) →
      (cell (A + (k + 1) * Q) 1 = true ∨
        (cell (A + (k + 1) * Q) 1 = false ∧ cell (A + (k + 1) * Q) 2 = true)) := by
    intro k h
    rcases h with h | h
    · exact Or.inl (s0_step k h)
    · exact s1_step k h
  let Z2 : Nat → Prop := fun k => (∀ p : Nat, 1 ≤ p → p ≤ r + 2 → cell (A + k * Q) p = false) ∧
    cell (A + k * Q) ((r + 2 + 1 : Nat) : Int) = true
  -- outside the exceptional class r + 2, the state is in class 0 or 1 two periods later
  have two_step : ∀ k, ¬ Z2 k → (cell (A + (k + 2) * Q) 1 = true ∨
        (cell (A + (k + 2) * Q) 1 = false ∧ cell (A + (k + 2) * Q) 2 = true)) := by
    intro k hz
    have hA1 : 1 ≤ A + k * Q := by omega
    obtain ⟨ℓ, hwℓ, hbℓ⟩ := first_black (A + k * Q) hA1
    have via : (cell (A + (k + 1) * Q) 1 = true ∨
        (cell (A + (k + 1) * Q) 1 = false ∧ cell (A + (k + 1) * Q) 2 = true)) →
        (cell (A + (k + 2) * Q) 1 = true ∨
        (cell (A + (k + 2) * Q) 1 = false ∧ cell (A + (k + 2) * Q) 2 = true)) := by
      intro h
      have := step01 (k + 1) h
      rwa [show k + 1 + 1 = k + 2 by omega] at this
    by_cases c2 : ℓ ≤ r
    · exact via (late k ℓ c2 hwℓ hbℓ)
    by_cases c3 : ℓ = r + 1
    · subst c3
      obtain ⟨h1, h2⟩ := period_z1 (A + k * Q) r (drvw k) (drvb1 k) (drvb2 k) hwℓ hbℓ
      rw [hnext k] at h1 h2
      exact via (Or.inr ⟨h1, h2⟩)
    by_cases c4 : ℓ = r + 2
    · subst c4
      exact absurd ⟨hwℓ, hbℓ⟩ hz
    by_cases c5 : ℓ = r + 3
    · subst c5
      obtain ⟨h1, h2, h3⟩ := period_z3 (A + k * Q) r (drvw k) (drvb1 k) (drvb2 k) hwℓ hbℓ
      rw [hnext k] at h1 h2 h3
      have := late (k + 1) 2 (by omega) (fun p hp1 hp2 => by
        by_cases hp : p = 1
        · subst hp; simpa using h1
        · have : p = 2 := by omega
          subst this; simpa using h2) (by simpa using h3)
      rwa [show k + 1 + 1 = k + 2 by omega] at this
    · have hz4 : 4 ≤ ℓ - r := by omega
      obtain ⟨h1, h2⟩ := period_z4 (A + k * Q) r (drvw k) (drvb1 k) (drvb2 k) (ℓ - r) hz4
        (fun p hp1 hp2 => hwℓ p hp1 (by omega)) (by rw [show r + (ℓ - r) + 1 = ℓ + 1 by omega]; exact hbℓ)
      rw [hnext k] at h1 h2
      exact via (Or.inr ⟨h1, h2⟩)
  -- column 1 over one period in each of the three possible eventual classes
  have pattern0 : ∀ k, cell (A + k * Q) 1 = true → ∀ i, i < Q →
      cell (A + k * Q + i) 1 = decide (i ≤ r) := by
    intro k hk i hi
    obtain ⟨hblk, c1, _⟩ := period_lock (A + k * Q) r (drvw k) (drvb1 k) (drvb2 k) hr 0
      (by omega) (fun p h1 h2 => by omega) (by simpa using hk)
    by_cases hir : i ≤ r
    · rw [hblk i (by omega) hir]; simp [hir]
    · have : i = r + 1 := by omega
      subst this; rw [show A + k * Q + (r + 1) = A + k * Q + r + 1 by omega, c1]; simp
  have pattern1 : ∀ k, (cell (A + k * Q) 1 = false ∧ cell (A + k * Q) 2 = true) → ∀ i, i < Q →
      cell (A + k * Q + i) 1 = decide (1 ≤ i ∧ i ≤ r) := by
    intro k hk i hi
    have hw1 : ∀ p : Nat, 1 ≤ p → p ≤ 1 → cell (A + k * Q) p = false := fun p hp1 hp2 => by
      have : p = 1 := by omega
      subst this; simpa using hk.1
    have hb1' : cell (A + k * Q) ((1 + 1 : Nat) : Int) = true := by simpa using hk.2
    have hfront := (front_moves (A + k * Q) 1 r (drvw k) hw1 hb1' 1 (by omega) (Nat.le_refl 1)).2
    rw [show 1 - 1 + 1 = 1 by omega] at hfront
    have hblk : ∀ j, 1 ≤ j → j ≤ r → cell (A + k * Q + j) 1 = true := by
      intro j h1 h2
      have := black_stays (A + k * Q + 1) (r - 1) (fun m hm => by
        have := drvw k (1 + m) (by omega)
        rwa [show A + k * Q + (1 + m) = A + k * Q + 1 + m by omega] at this)
        (by simpa using hfront) (j - 1) (by omega)
      rwa [show A + k * Q + 1 + (j - 1) = A + k * Q + j by omega] at this
    have c1 : cell (A + k * Q + r + 1) 1 = false := by
      show rule (cell (A + k * Q + r) (1 - 1)) (cell (A + k * Q + r) 1) (cell (A + k * Q + r) (1 + 1)) = false
      rw [show (1 : Int) - 1 = 0 by rfl, drvb1 k, hblk r (by omega) (Nat.le_refl r)]
      rfl
    by_cases hi0 : i = 0
    · subst hi0; simpa using hk.1
    by_cases hir : i ≤ r
    · rw [hblk i (by omega) hir]; simp; omega
    · have : i = r + 1 := by omega
      subst this; rw [show A + k * Q + (r + 1) = A + k * Q + r + 1 by omega, c1]; simp
  have z2_pattern : ∀ k, Z2 k → ∀ i, i < Q → cell (A + k * Q + i) 1 = decide (i = r + 1) := by
    intro k hk i hi
    obtain ⟨hw0, c1⟩ := period_z2 (A + k * Q) r (drvw k) (drvb1 k) hk.1 hk.2
    by_cases hir : i ≤ r
    · rw [hw0 i hir]; simp; omega
    · have : i = r + 1 := by omega
      subst this; rw [show A + k * Q + (r + 1) = A + k * Q + r + 1 by omega, c1]; simp
  have h1 : EventuallyPeriodic (fun t => cell t (0 + 1)) := by
    by_cases hall : ∀ k, Z2 k
    · exact periodic_blocks A Q hQ (fun i => decide (i = r + 1)) (fun j i hi => z2_pattern j (hall j) i hi)
    · have hex : ∃ k, ¬ Z2 k := Classical.byContradiction fun hne => hall fun k =>
        Classical.byContradiction fun hk => hne ⟨k, hk⟩
      obtain ⟨k, hk⟩ := hex
      have hU : ∀ j, cell (A + (k + 2 + j) * Q) 1 = true ∨
          (cell (A + (k + 2 + j) * Q) 1 = false ∧ cell (A + (k + 2 + j) * Q) 2 = true) := by
        intro j
        induction j with
        | zero => simpa using two_step k hk
        | succ j ih =>
          rw [show k + 2 + (j + 1) = (k + 2 + j) + 1 by omega]
          exact step01 _ ih
      by_cases hs0 : ∃ j, cell (A + (k + 2 + j) * Q) 1 = true
      · obtain ⟨j0, hj0⟩ := hs0
        have hall0 : ∀ j, cell (A + (k + 2 + j0 + j) * Q) 1 = true := by
          intro j
          induction j with
          | zero => simpa using hj0
          | succ j ih =>
            rw [show k + 2 + j0 + (j + 1) = (k + 2 + j0 + j) + 1 by omega]
            exact s0_step _ ih
        refine periodic_blocks (A + (k + 2 + j0) * Q) Q hQ (fun i => decide (i ≤ r)) (fun j i hi => ?_)
        have := pattern0 (k + 2 + j0 + j) (hall0 j) i hi
        have hm : (k + 2 + j0 + j) * Q = (k + 2 + j0) * Q + j * Q := Nat.add_mul (k + 2 + j0) j Q
        rwa [hm, show A + ((k + 2 + j0) * Q + j * Q) + i = A + (k + 2 + j0) * Q + j * Q + i by omega] at this
      · have hall1 : ∀ j, cell (A + (k + 2 + j) * Q) 1 = false ∧ cell (A + (k + 2 + j) * Q) 2 = true := by
          intro j
          rcases hU j with h | h
          · exact absurd ⟨j, h⟩ hs0
          · exact h
        refine periodic_blocks (A + (k + 2) * Q) Q hQ (fun i => decide (1 ≤ i ∧ i ≤ r)) (fun j i hi => ?_)
        have := pattern1 (k + 2 + j) (hall1 j) i hi
        have hm : (k + 2 + j) * Q = (k + 2) * Q + j * Q := Nat.add_mul (k + 2) j Q
        rwa [hm, show A + ((k + 2) * Q + j * Q) + i = A + (k + 2) * Q + j * Q + i by omega] at this
  have h0 : EventuallyPeriodic (fun t => cell t 0) := ⟨T, Q, hQ, hper⟩
  exact not_adjacent 0 h0 h1

end AbsorbWhiteGe8

#print axioms AbsorbWhiteGe8.no_white_run_11_ge8
