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
# Every diagonal of rule 30 is periodic

The rule-30 pattern from a single black cell, read along diagonals parallel to its two edges:

* `R j t = cell t (t − j)`, the `j`-th diagonal from the right edge, and
* `D j t = cell t (j − t)`, the `j`-th diagonal from the left edge.

Both families obey a recurrence that feeds each diagonal from the two before it:

    R_{j+2}(t + 1) = R_{j+2}(t) xor (R_{j+1}(t) or R_j(t))
    D_{j+2}(t + 1) = D_j(t) xor (D_{j+1}(t) or D_{j+2}(t))

* `R_periodic`: **every right diagonal is periodic from the start**, with period `2^j`. The
  diagonal accumulates the parity of its input, and a periodic input adds the same parity over
  each period, so two periods return to the start.
* `D_periodic`: **every left diagonal is eventually periodic**, with period `2^j`. A one-bit state
  driven by an eventually periodic input: among the three states one and two input periods apart,
  two agree, and from then on they agree forever.
* `center_eq_parity`: unrolling the right-diagonal recurrence, the center cell at time `t ≥ 2` is
  the parity of the number of rows `s < t` with a black cell at `s − t + 1` or `s − t + 2`.

The center column is the diagonal of diagonals: `center t = R t t = D t t`
(`center_eq_R`, `center_eq_D`). The period bound `2^j` exceeds `j`, so these theorems say nothing
about the center column. Wolfram notes the left-side periods grow very slowly and the right-side
ones exponentially; Rowland (*Local Nested Structure in Rule 30*, Complex Systems 16 (2006))
proves the left-side period doubling.
-/

namespace Ruliology.CellularAutomata
namespace Rule30Diagonals

open Rule30Jen

/-- The `j`-th diagonal from the right edge. -/
def R (j t : Nat) : Bool := cell t ((t : Int) - j)

/-- The `j`-th diagonal from the left edge. -/
def D (j t : Nat) : Bool := cell t ((j : Int) - t)

theorem center_eq_R (t : Nat) : cell t 0 = R t t := by simp [R]

theorem center_eq_D (t : Nat) : cell t 0 = D t t := by simp [D]

/-! ### Local rule, with positions up to arithmetic -/

theorem cell_congr {t : Nat} {p q : Int} (h : p = q) : cell t p = cell t q := h ▸ rfl

theorem cell_succ' (t : Nat) (p a b c : Int) (ha : a = p - 1) (hb : b = p) (hc : c = p + 1) :
    cell (t + 1) p = rule (cell t a) (cell t b) (cell t c) := by
  subst ha hb hc; rfl

theorem cell_eq_false_of_gt : ∀ (t : Nat) (p : Int), (t : Int) < p → cell t p = false
  | 0, p, h => by simp [cell]; omega
  | t + 1, p, h => by
    show rule (cell t (p - 1)) (cell t p) (cell t (p + 1)) = false
    rw [cell_eq_false_of_gt t (p - 1) (by omega), cell_eq_false_of_gt t p (by omega),
      cell_eq_false_of_gt t (p + 1) (by omega)]
    rfl

/-! ### The right edge -/

/-- The rightmost black cell is at `t`. -/
theorem R_zero : ∀ t, R 0 t = true
  | 0 => rfl
  | t + 1 => by
    have e : R 0 (t + 1) = rule (R 0 t) (cell t ((t : Int) + 1)) (cell t ((t : Int) + 2)) :=
      cell_succ' t _ _ _ _ (by omega) (by omega) (by omega)
    rw [e, R_zero t, cell_eq_false_of_gt t _ (by omega), cell_eq_false_of_gt t _ (by omega)]
    rfl

theorem R_one_succ (t : Nat) : R 1 (t + 1) = !R 1 t := by
  have e : R 1 (t + 1) = rule (R 1 t) (R 0 t) (cell t ((t : Int) + 1)) :=
    cell_succ' t _ _ _ _ (by omega) (by omega) (by omega)
  rw [e, R_zero t, cell_eq_false_of_gt t _ (by omega)]
  cases R 1 t <;> rfl

theorem R_step (j t : Nat) : R (j + 2) (t + 1) = xor (R (j + 2) t) (R (j + 1) t || R j t) :=
  cell_succ' t _ _ _ _ (by omega) (by omega)
    (by omega)

/-! ### Periodicity of the right diagonals -/

/-- A sequence that accumulates the parity of a periodic input is periodic with twice the
period. -/
theorem xor_accum_periodic {x g : Nat → Bool} {L : Nat} (hx : ∀ t, x (t + 1) = xor (x t) (g t))
    (hg : ∀ t, g (t + L) = g t) : ∀ t, x (t + 2 * L) = x t := by
  -- `h t` is the parity that one period adds; it does not depend on `t`
  have hconst : ∀ t, xor (x (t + L)) (x t) = xor (x L) (x 0) := by
    intro t
    induction t with
    | zero => rw [Nat.zero_add]
    | succ t ih =>
      rw [show t + 1 + L = (t + L) + 1 by omega, hx (t + L), hx t, hg t, ← ih]
      cases x (t + L) <;> cases x t <;> cases g t <;> rfl
  intro t
  have h1 := hconst t
  have h2 := hconst (t + L)
  rw [show t + L + L = t + 2 * L by omega] at h2
  revert h1 h2
  cases x (t + 2 * L) <;> cases x (t + L) <;> cases x t <;> cases xor (x L) (x 0) <;> simp

theorem periodic_double {f : Nat → Bool} {L : Nat} (h : ∀ t, f (t + L) = f t) :
    ∀ t, f (t + 2 * L) = f t := by
  intro t; rw [show t + 2 * L = (t + L) + L by omega, h, h]

/-- **Every right diagonal is periodic from the start, with period `2^j`.** -/
theorem R_periodic : ∀ j t, R j (t + 2 ^ j) = R j t := by
  have pair : ∀ j, (∀ t, R j (t + 2 ^ j) = R j t) ∧ (∀ t, R (j + 1) (t + 2 ^ (j + 1)) = R (j + 1) t) := by
    intro j
    induction j with
    | zero =>
      refine ⟨fun t => by rw [R_zero, R_zero], fun t => ?_⟩
      rw [show t + 2 ^ (0 + 1) = (t + 1) + 1 by simp, R_one_succ, R_one_succ]
      cases R 1 t <;> rfl
    | succ j ih =>
      refine ⟨ih.2, ?_⟩
      have hg : ∀ t, (R (j + 1) (t + 2 ^ (j + 1)) || R j (t + 2 ^ (j + 1))) =
          (R (j + 1) t || R j t) := by
        intro t
        rw [ih.2 t, show 2 ^ (j + 1) = 2 * 2 ^ j by rw [Nat.pow_succ]; omega,
          periodic_double ih.1 t]
      have := xor_accum_periodic (x := R (j + 2)) (g := fun t => R (j + 1) t || R j t)
        (L := 2 ^ (j + 1)) (fun t => R_step j t) hg
      intro t
      rw [show 2 ^ (j + 1 + 1) = 2 * 2 ^ (j + 1) by rw [Nat.pow_succ]; omega]
      exact this t
  exact fun j => (pair j).1

/-! ### The left edge and the left diagonals -/

/-- The leftmost black cell is at `−t`. -/
theorem D_zero (t : Nat) : D 0 t = true := by
  have e : D 0 t = cell t (-(t : Int)) := cell_congr (by omega)
  rw [e]; exact cell_left_edge t

theorem D_one (t : Nat) : D 1 (t + 1) = true := by
  have e : D 1 (t + 1) = rule (cell t (-(t : Int) - 1)) (D 0 t) (D 1 t) :=
    cell_succ' t _ _ _ _ (by omega) (by omega)
      (by omega)
  rw [e, D_zero t, cell_eq_false_of_lt t _ (by omega)]
  rfl

theorem D_step (j t : Nat) : D (j + 2) (t + 1) = xor (D j t) (D (j + 1) t || D (j + 2) t) :=
  cell_succ' t _ _ _ _ (by omega) (by omega)
    (by omega)

/-- A one-bit state driven by an eventually periodic transition is eventually periodic with
twice the period. Among the states `L` and `2L` steps after `T`, two agree, and two runs of the
same recurrence that agree once agree from then on. -/
theorem transducer_periodic {x : Nat → Bool} {F : Nat → Bool → Bool} {T L : Nat}
    (hx : ∀ t, T ≤ t → x (t + 1) = F t (x t)) (hF : ∀ t, T ≤ t → F (t + L) = F t) :
    ∀ t, T + L ≤ t → x (t + 2 * L) = x t := by
  have hFk : ∀ k t, T ≤ t → F (t + k * L) = F t := by
    intro k
    induction k with
    | zero => intro t _; simp
    | succ k ih =>
      intro t ht
      rw [show t + (k + 1) * L = (t + k * L) + L by rw [Nat.succ_mul]; omega,
        hF _ (by omega), ih t ht]
  -- runs started `a` and `b` periods after `T` that agree once agree forever
  have agree : ∀ a b, x (T + a * L) = x (T + b * L) →
      ∀ s, x (T + a * L + s) = x (T + b * L + s) := by
    intro a b hab s
    induction s with
    | zero => exact hab
    | succ s ih =>
      rw [← Nat.add_assoc, ← Nat.add_assoc, hx _ (by omega), hx _ (by omega),
        show T + a * L + s = (T + s) + a * L by omega, show T + b * L + s = (T + s) + b * L by omega,
        hFk a (T + s) (by omega), hFk b (T + s) (by omega)]
      rw [show (T + s) + a * L = T + a * L + s by omega,
        show (T + s) + b * L = T + b * L + s by omega, ih]
  intro t ht
  -- pigeonhole on the three states at `T`, `T + L`, `T + 2L`
  have h01 := agree 0 1; have h12 := agree 1 2; have h02 := agree 0 2
  simp only [Nat.zero_mul, Nat.add_zero, Nat.one_mul] at h01 h12 h02
  have pig : x T = x (T + L) ∨ x (T + L) = x (T + 2 * L) ∨ x T = x (T + 2 * L) := by
    cases x T <;> cases x (T + L) <;> cases x (T + 2 * L) <;> simp
  rcases pig with e | e | e
  · have hA := h01 e (t - T)
    have hB := h01 e (t - T + L)
    rw [show T + (t - T) = t by omega, show T + L + (t - T) = t + L by omega] at hA
    rw [show T + (t - T + L) = t + L by omega, show T + L + (t - T + L) = t + 2 * L by omega] at hB
    rw [← hB, ← hA]
  · have hA := h12 e (t - T - L)
    have hB := h12 e (t - T)
    rw [show T + L + (t - T - L) = t by omega, show T + 2 * L + (t - T - L) = t + L by omega] at hA
    rw [show T + L + (t - T) = t + L by omega, show T + 2 * L + (t - T) = t + 2 * L by omega] at hB
    rw [← hB, ← hA]
  · have h := h02 e (t - T)
    rw [show T + (t - T) = t by omega, show T + 2 * L + (t - T) = t + 2 * L by omega] at h
    exact h.symm

/-- **Every left diagonal is eventually periodic, with period `2^j`.** -/
theorem D_periodic : ∀ j, ∃ T, ∀ t, T ≤ t → D j (t + 2 ^ j) = D j t := by
  have pair : ∀ j, (∃ T, ∀ t, T ≤ t → D j (t + 2 ^ j) = D j t) ∧
      (∃ T, ∀ t, T ≤ t → D (j + 1) (t + 2 ^ (j + 1)) = D (j + 1) t) := by
    intro j
    induction j with
    | zero =>
      refine ⟨⟨0, fun t _ => by rw [D_zero, D_zero]⟩, ⟨1, fun t ht => ?_⟩⟩
      obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
      rw [show s + 1 + 2 ^ (0 + 1) = (s + 2) + 1 by simp, D_one, D_one]
    | succ j ih =>
      refine ⟨ih.2, ?_⟩
      obtain ⟨⟨Ta, ha⟩, ⟨Tb, hb⟩⟩ := ih
      have hp := Nat.two_pow_pos j
      have ha2 : ∀ t, Ta ≤ t → D j (t + 2 ^ (j + 1)) = D j t := by
        intro t ht
        rw [show t + 2 ^ (j + 1) = (t + 2 ^ j) + 2 ^ j by rw [Nat.pow_succ]; omega,
          ha _ (by omega), ha t ht]
      refine ⟨max Ta Tb + 2 ^ (j + 1), fun t ht => ?_⟩
      have := transducer_periodic (x := D (j + 2))
        (F := fun t b => xor (D j t) (D (j + 1) t || b)) (T := max Ta Tb) (L := 2 ^ (j + 1))
        (fun t _ => D_step j t)
        (fun t ht => by
          funext b
          simp only
          rw [ha2 t (by omega), hb t (by omega)])
        t (by omega)
      rw [show 2 ^ (j + 1 + 1) = 2 * 2 ^ (j + 1) by rw [Nat.pow_succ]; omega]
      exact this
  exact fun j => (pair j).1

/-! ### The center column as a parity -/

theorem parity_succ (n : Nat) : ((n + 1) % 2 == 1) = !(n % 2 == 1) := by
  rcases Nat.mod_two_eq_zero_or_one n with h | h
  · have h' : (n + 1) % 2 = 1 := by omega
    simp [h, h']
  · have h' : (n + 1) % 2 = 0 := by omega
    simp [h, h']

/-- A sequence that starts at `false` and accumulates `g` is the parity of the number of times
`g` was true. -/
theorem xor_accum_parity {x g : Nat → Bool} (h0 : x 0 = false)
    (hx : ∀ t, x (t + 1) = xor (x t) (g t)) :
    ∀ t, x t = (((List.range t).filter g).length % 2 == 1) := by
  intro t
  induction t with
  | zero => simp [h0]
  | succ t ih =>
    rw [hx t, ih, List.range_succ, List.filter_append, List.length_append]
    cases hg : g t
    · simp [hg]
    · simp only [List.filter_cons, hg, ↓reduceIte, List.filter_nil, List.length_cons,
        List.length_nil, Nat.zero_add, Bool.xor_true]
      exact (parity_succ _).symm

/-- Each right diagonal (from the third on) is the parity of how often one of the two diagonals
before it was black. -/
theorem R_eq_parity (j t : Nat) :
    R (j + 2) t = (((List.range t).filter (fun s => R (j + 1) s || R j s)).length % 2 == 1) :=
  xor_accum_parity (x := R (j + 2)) (by simp [R, cell]; omega) (fun t => R_step j t) t

/-- **The center column as a parity**: for `t ≥ 2`, the center cell at time `t` is black exactly
when an odd number of earlier rows `s < t` have a black cell at position `s − t + 1` or
`s − t + 2`. -/
theorem center_eq_parity (t : Nat) (ht : 2 ≤ t) :
    cell t 0 = (((List.range t).filter
      (fun s => cell s ((s : Int) - t + 1) || cell s ((s : Int) - t + 2))).length % 2 == 1) := by
  obtain ⟨j, rfl⟩ : ∃ j, t = j + 2 := ⟨t - 2, by omega⟩
  rw [center_eq_R, R_eq_parity]
  congr 3
  apply List.filter_congr
  intro s _
  rw [cell_congr (show (s : Int) - ((j + 2 : Nat) : Int) + 1 = (s : Int) - ((j + 1 : Nat) : Int)
      by omega),
    cell_congr (show (s : Int) - ((j + 2 : Nat) : Int) + 2 = (s : Int) - (j : Int) by omega)]
  rfl

end Rule30Diagonals
end Ruliology.CellularAutomata


/-!
# Right-diagonal periods are read off from the rows at times `2^e`

`R j t = cell t (t - j)` is the `j`-th diagonal from the right edge (`Rule30Diagonals`).

* `R_period_iff`: for all `e J`, the diagonals `R 0, …, R J` all have period dividing `2^e`
  **iff** the `J` cells just left of the right edge in row `2^e` are white:
  `cell (2^e) (2^e - j) = false` for `1 ≤ j ≤ J`.

Proof: a one-bit accumulator `x (t+1) = x t xor g t` with `L`-periodic input satisfies
`x (t + L) = x t xor (x L xor x 0)`; the diagonal recurrence makes `R j` such an accumulator of
`R (j-1) || R (j-2)`, and `R j 0 = false` for `j ≥ 1`.
-/

namespace Ruliology.CellularAutomata
namespace Rule30DiagonalPeriods

open Rule30Jen Rule30Diagonals

/-- A one-bit accumulator driven by an `L`-periodic input gains a fixed parity per period. -/
theorem xor_accum_shift {x g : Nat → Bool} {L : Nat} (hx : ∀ t, x (t + 1) = xor (x t) (g t))
    (hg : ∀ t, g (t + L) = g t) : ∀ t, x (t + L) = xor (x t) (xor (x L) (x 0)) := by
  intro t
  induction t with
  | zero => rw [Nat.zero_add]; cases x L <;> cases x 0 <;> rfl
  | succ t ih =>
    rw [show t + 1 + L = (t + L) + 1 by omega, hx (t + L), hx t, hg t, ih]
    cases x t <;> cases g t <;> cases x L <;> cases x 0 <;> rfl

theorem R_start {j : Nat} (hj : 1 ≤ j) : R j 0 = false := by
  simp [R, cell]
  omega

theorem R_one_step (t : Nat) : R 1 (t + 1) = xor (R 1 t) true := by
  rw [R_one_succ]; cases R 1 t <;> rfl

/-- **The right diagonals `0..J` all have period dividing `2^e` iff row `2^e` ends with
`J` white cells before its right-edge cell.** -/
theorem R_period_iff (e J : Nat) :
    (∀ j, j ≤ J → ∀ t, R j (t + 2 ^ e) = R j t) ↔
    (∀ j, 1 ≤ j → j ≤ J → cell (2 ^ e) (((2 ^ e : Nat) : Int) - j) = false) := by
  constructor
  · intro h j hj1 hjJ
    have h0 := h j hjJ 0
    rw [Nat.zero_add] at h0
    show R j (2 ^ e) = false
    rw [h0, R_start hj1]
  · intro h
    have hR : ∀ j, 1 ≤ j → j ≤ J → R j (2 ^ e) = false := fun j h1 h2 => h j h1 h2
    have key : ∀ j, (j ≤ J → ∀ t, R j (t + 2 ^ e) = R j t) ∧
        (j + 1 ≤ J → ∀ t, R (j + 1) (t + 2 ^ e) = R (j + 1) t) := by
      intro j
      induction j with
      | zero =>
        refine ⟨fun _ t => by rw [R_zero, R_zero], fun h1 t => ?_⟩
        have := xor_accum_shift (x := R 1) (g := fun _ => true) (L := 2 ^ e)
          (fun t => R_one_step t) (fun _ => rfl) t
        rw [this, hR 1 (by omega) h1, R_start (by omega)]
        cases R 1 t <;> rfl
      | succ j ih =>
        refine ⟨ih.2, fun h2 t => ?_⟩
        have p1 := ih.2 (by omega)
        have p0 := ih.1 (by omega)
        have hg : ∀ t, (R (j + 1) (t + 2 ^ e) || R j (t + 2 ^ e)) = (R (j + 1) t || R j t) := by
          intro t; rw [p1 t, p0 t]
        have := xor_accum_shift (x := R (j + 2)) (g := fun t => R (j + 1) t || R j t)
          (L := 2 ^ e) (fun t => R_step j t) hg t
        rw [this, hR (j + 2) (by omega) h2, R_start (by omega)]
        cases R (j + 2) t <;> rfl
    exact fun j hj => (key j).1 hj

/-- Consequence: if the diagonals `0..J` have period dividing `2^e`, rows `t` and `t + m·2^e`
agree on the `J + 1` cells at their right ends. -/
theorem right_end_copy (e J : Nat) (h : ∀ j, j ≤ J → ∀ t, R j (t + 2 ^ e) = R j t)
    (m t j : Nat) (hj : j ≤ J) : R j (t + m * 2 ^ e) = R j t := by
  induction m with
  | zero => simp
  | succ m ih => rw [show t + (m + 1) * 2 ^ e = (t + m * 2 ^ e) + 2 ^ e by
      rw [Nat.succ_mul]; omega, h j hj, ih]

end Rule30DiagonalPeriods
end Ruliology.CellularAutomata

#print axioms Ruliology.CellularAutomata.Rule30DiagonalPeriods.R_period_iff
#print axioms Ruliology.CellularAutomata.Rule30DiagonalPeriods.right_end_copy
