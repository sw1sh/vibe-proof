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

namespace Ruliology.CellularAutomata
namespace Rule30Prize
open Rule30Jen
/-- The center column (copied verbatim from Rule30Prize.lean). -/
def center (t : Nat) : Bool := cell t 0
end Rule30Prize
end Ruliology.CellularAutomata


/-!
# Rule 30: long black runs in the center column are absorbing on the right

* `nine_black`: (**Lemma A**) if a column is black for 9 consecutive steps, then right after them
  the next two columns are white, black. Finite core checked by `decide +kernel` (2048 cases).
* `black_shield`: (**Lemma A***) if a column is black for `9 j` consecutive steps, then right after
  them the next `2 j` columns read `(white black)^j`.
* `cone_agree`: two times whose rows agree on columns `1..n` and whose center columns agree from
  then on keep agreeing on the shrinking cone.
* `no_long_black_run`: (**Theorem B**) if the center column is eventually periodic with period `P`
  and one period contains a black run of length `r ≥ 9 ⌈(P - r + 9) / 2⌉`, contradiction: column 1
  would be eventually periodic too, against Jen's theorem.
-/

namespace AbsorbRight

open Ruliology.CellularAutomata.Rule30Jen
open Ruliology.CellularAutomata.Rule30Prize

/-- The cells at columns `p, p+1, …, p+n-1` at time `t`. -/
def rowAt (t : Nat) (p : Int) : Nat → List Bool
  | 0 => []
  | n + 1 => cell t p :: rowAt t (p + 1) n

theorem length_rowAt (t : Nat) : ∀ (n : Nat) (p : Int), (rowAt t p n).length = n
  | 0, _ => rfl
  | n + 1, p => by simp [rowAt, length_rowAt t n (p + 1)]

/-- One rule-30 step on a finite row with left neighbour `l`; one cell shorter. -/
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

/-- `k` steps with a black left neighbour. -/
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

/-- Finite core of Lemma A: all `2^11` rows. -/
theorem nine_black_core : ∀ L ∈ allLists 11, runBlack 9 L = [false, true] := by
  decide +kernel

/-- **Lemma A.** A column black for 9 consecutive steps forces white, black right after them in
the next two columns. -/
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

/-- **Lemma A\*.** A column black for `9 j` consecutive steps forces `(white black)^j` in the next
`2 j` columns right after them. -/
theorem black_shield (m : Int) : ∀ (j t : Nat), (∀ s, s < 9 * j → cell (t + s) m = true) →
    ∀ i : Nat, 1 ≤ i → i ≤ j →
      cell (t + 9 * j) (m + 2 * (i : Int) - 1) = false ∧ cell (t + 9 * j) (m + 2 * (i : Int)) = true
  | 0, _, _, i, hi1, hij => by omega
  | j + 1, t, h, i, hi1, hij => by
    by_cases hi : i ≤ j
    · have ih := black_shield m j (t + 9) (fun s hs => by
        have := h (9 + s) (by omega)
        rwa [show t + (9 + s) = t + 9 + s by omega] at this) i hi1 hi
      rwa [show t + 9 + 9 * j = t + 9 * (j + 1) by omega] at ih
    · have hieq : i = j + 1 := by omega
      subst hieq
      -- column m + 2 j is black at the 9 times t + 9 j + s, s < 9
      have hcol : ∀ s, s < 9 → cell (t + 9 * j + s) (m + 2 * (j : Int)) = true := by
        intro s hs
        by_cases hj : j = 0
        · subst hj
          have := h s (by omega)
          simpa using this
        · have ih := black_shield m j (t + s) (fun s' hs' => by
            have := h (s + s') (by omega)
            rwa [show t + (s + s') = t + s + s' by omega] at this) j (by omega) (by omega)
          rw [show t + s + 9 * j = t + 9 * j + s by omega] at ih
          exact ih.2
      have hA := nine_black (t + 9 * j) (m + 2 * (j : Int)) hcol
      rw [show t + 9 * j + 9 = t + 9 * (j + 1) by omega,
        show m + 2 * (j : Int) + 1 = m + 2 * ((j + 1 : Nat) : Int) - 1 by omega,
        show m + 2 * (j : Int) + 2 = m + 2 * ((j + 1 : Nat) : Int) by omega] at hA
      exact hA

/-- Agreement in the shrinking cone of the right half, driven by column `0`. -/
theorem cone_agree (t0 t1 n : Nat) (hdrv : ∀ s, cell (t0 + s) 0 = cell (t1 + s) 0)
    (hrow : ∀ p : Int, 1 ≤ p → p ≤ n → cell t0 p = cell t1 p) :
    ∀ s : Nat, ∀ p : Int, 1 ≤ p → p + s ≤ n → cell (t0 + s) p = cell (t1 + s) p
  | 0, p, h1, h2 => by simpa using hrow p h1 (by omega)
  | s + 1, p, h1, h2 => by
    show rule (cell (t0 + s) (p - 1)) (cell (t0 + s) p) (cell (t0 + s) (p + 1)) =
      rule (cell (t1 + s) (p - 1)) (cell (t1 + s) p) (cell (t1 + s) (p + 1))
    have hl : cell (t0 + s) (p - 1) = cell (t1 + s) (p - 1) := by
      by_cases hp : p = 1
      · rw [show p - 1 = 0 by omega]; exact hdrv s
      · exact cone_agree t0 t1 n hdrv hrow s (p - 1) (by omega) (by omega)
    rw [hl, cone_agree t0 t1 n hdrv hrow s p h1 (by omega),
      cone_agree t0 t1 n hdrv hrow s (p + 1) (by omega) (by omega)]

/-- **Theorem B.** If the center column is periodic with period `P` from time `T` on, no period
can contain a black run of length `r` with `9 ⌈(P - r + 9) / 2⌉ ≤ r`. -/
theorem no_long_black_run (T P r t1 : Nat) (hper : ∀ t, T ≤ t → center (t + P) = center t)
    (ht1 : T ≤ t1) (hr : r ≤ P) (hrun : ∀ s, s < r → center (t1 + s) = true)
    (hlong : 9 * ((P - r + 10) / 2) ≤ r) : False := by
  have hP : 0 < P := by omega
  -- j = ⌈(P - r + 9) / 2⌉
  have hj1 : P - r + 9 ≤ 2 * ((P - r + 10) / 2) := by omega
  generalize hjdef : (P - r + 10) / 2 = j at hj1 hlong
  have hperk : ∀ k t, T ≤ t → center (t + k * P) = center t := periodic_mul hper
  have hblack : ∀ k s, s < r → cell (t1 + k * P + s) 0 = true := by
    intro k s hs
    have := hperk k (t1 + s) (by omega)
    show center (t1 + k * P + s) = true
    rw [show t1 + k * P + s = t1 + s + k * P by omega, this]
    exact hrun s hs
  -- the row right after each black run reads (white black)^j on columns 1..2j
  have hrowk : ∀ k i, 1 ≤ i → i ≤ j →
      cell (t1 + r + k * P) (2 * (i : Int) - 1) = false ∧ cell (t1 + r + k * P) (2 * (i : Int)) = true := by
    intro k i hi1 hij
    have := black_shield 0 j (t1 + k * P + (r - 9 * j)) (fun s hs => by
        have := hblack k (r - 9 * j + s) (by omega)
        rwa [show t1 + k * P + (r - 9 * j + s) = t1 + k * P + (r - 9 * j) + s by omega] at this)
      i hi1 hij
    rw [show t1 + k * P + (r - 9 * j) + 9 * j = t1 + r + k * P by omega] at this
    simpa using this
  have hrowagree : ∀ k, ∀ p : Int, 1 ≤ p → p ≤ (2 * j : Nat) →
      cell (t1 + r) p = cell (t1 + r + k * P) p := by
    intro k p hp1 hp2
    have a0 := hrowk 0
    simp only [Nat.zero_mul, Nat.add_zero] at a0
    by_cases hpar : p % 2 = 0
    · have hi : p = 2 * (((p / 2).toNat : Nat) : Int) := by omega
      rw [hi, (a0 _ (by omega) (by omega)).2, (hrowk k _ (by omega) (by omega)).2]
    · have hi : p = 2 * ((((p + 1) / 2).toNat : Nat) : Int) - 1 := by omega
      rw [hi, (a0 _ (by omega) (by omega)).1, (hrowk k _ (by omega) (by omega)).1]
  have hdrv : ∀ k s, cell (t1 + r + s) 0 = cell (t1 + r + k * P + s) 0 := by
    intro k s
    have := hperk k (t1 + r + s) (by omega)
    show center (t1 + r + s) = center (t1 + r + k * P + s)
    rw [show t1 + r + k * P + s = t1 + r + s + k * P by omega, this]
  -- column 1 is white 9 steps into a black run
  have white1 : ∀ t', (∀ s', s' < 9 → cell (t' + s') 0 = true) → cell (t' + 9) 1 = false := by
    intro t' h
    have := (nine_black t' 0 h).1
    simpa using this
  have hcol : ∀ k s, s < P → cell (t1 + r + s) 1 = cell (t1 + r + k * P + s) 1 := by
    intro k s hs
    by_cases hs1 : s + 1 ≤ 2 * j
    · exact cone_agree (t1 + r) (t1 + r + k * P) (2 * j) (hdrv k) (hrowagree k) s 1 (by omega)
        (by omega)
    · have hPk : (k + 1) * P = k * P + P := Nat.succ_mul k P
      have a : cell (t1 + r + s) 1 = false := by
        have := white1 (t1 + r + s - 9) (fun s' hs' => by
          have := hblack 1 (s - 9 + s' - (P - r)) (by omega)
          rwa [show t1 + 1 * P + (s - 9 + s' - (P - r)) = t1 + r + s - 9 + s' by omega] at this)
        rwa [show t1 + r + s - 9 + 9 = t1 + r + s by omega] at this
      have b : cell (t1 + r + k * P + s) 1 = false := by
        have := white1 (t1 + r + k * P + s - 9) (fun s' hs' => by
          have := hblack (k + 1) (s - 9 + s' - (P - r)) (by omega)
          rwa [hPk, show t1 + (k * P + P) + (s - 9 + s' - (P - r)) =
            t1 + r + k * P + s - 9 + s' by omega] at this)
        rwa [show t1 + r + k * P + s - 9 + 9 = t1 + r + k * P + s by omega] at this
      rw [a, b]
  -- column 1 is eventually periodic, contradicting Jen's theorem
  have h1 : EventuallyPeriodic (fun t => cell t (0 + 1)) := by
    refine ⟨t1 + r, P, hP, fun t ht => ?_⟩
    show cell (t + P) (0 + 1) = cell t (0 + 1)
    rw [show (0 : Int) + 1 = 1 by rfl]
    have hdm := Nat.div_add_mod (t - (t1 + r)) P
    generalize (t - (t1 + r)) / P = q at hdm
    have hmod := Nat.mod_lt (t - (t1 + r)) hP
    generalize (t - (t1 + r)) % P = s at hdm hmod
    have hq1 : (q + 1) * P = q * P + P := Nat.succ_mul q P
    have e1 := hcol q s hmod
    have e2 := hcol (q + 1) s hmod
    rw [hq1] at e2
    have hcomm : P * q = q * P := Nat.mul_comm P q
    rw [show t + P = t1 + r + (q * P + P) + s by omega, ← e2, e1,
      show t1 + r + q * P + s = t by omega]
  have h0 : EventuallyPeriodic (fun t => cell t 0) := ⟨T, P, hP, hper⟩
  exact not_adjacent 0 h0 h1

/-! ### A sharper, block-specific version of Theorem B

For a specific block `u` following the black run, a finite check (`Determined u j0`) replaces the
crude cone bound: if every row whose first `2 j0` cells read `(white black)^j0` produces the same
column-1 trace under the driver `u` followed by nine black cells, then a black run of length
`r ≥ max 9 (9 j0)` before `u` forces column 1 to be periodic. -/

/-- Column-1 trace of a finite row under a driver list: values at times `0 … ds.length`. -/
def traceCol1 : List Bool → List Bool → List Bool
  | [], row => [row.headD false]
  | c :: cs, row => row.headD false :: traceCol1 cs (stepRow c row)

/-- Column 1 at times `e, e+1, …, e+n`. -/
def colTrace (e : Nat) : Nat → List Bool
  | 0 => [cell e 1]
  | n + 1 => cell e 1 :: colTrace (e + 1) n

theorem colTrace_getD : ∀ (n e s : Nat), s ≤ n → (colTrace e n).getD s false = cell (e + s) 1
  | 0, e, s, h => by
    have : s = 0 := by omega
    subst this; rfl
  | n + 1, e, 0, _ => rfl
  | n + 1, e, s + 1, h => by
    show (colTrace (e + 1) n).getD s false = cell (e + (s + 1)) 1
    rw [colTrace_getD n (e + 1) s (by omega), show e + 1 + s = e + (s + 1) by omega]

theorem traceCol1_rowAt : ∀ (ds : List Bool) (e : Nat),
    (∀ i, i < ds.length → cell (e + i) 0 = ds.getD i false) →
    traceCol1 ds (rowAt e 1 (ds.length + 1)) = colTrace e ds.length
  | [], e, _ => rfl
  | c :: cs, e, h => by
    have h0 : cell e 0 = c := by simpa using h 0 (by simp)
    have hstep : stepRow c (rowAt e 1 (cs.length + 1 + 1)) = rowAt (e + 1) 1 (cs.length + 1) := by
      have := stepRow_rowAt e (cs.length + 1) 1
      rw [show (1 : Int) - 1 = 0 by rfl, h0] at this
      exact this
    have ih := traceCol1_rowAt cs (e + 1) (fun i hi => by
      have := h (i + 1) (by simp; omega)
      rw [show e + (i + 1) = e + 1 + i by omega] at this
      simpa using this)
    show cell e 1 :: traceCol1 cs (stepRow c (rowAt e 1 (cs.length + 1 + 1))) =
      cell e 1 :: colTrace (e + 1) cs.length
    rw [hstep, ih]

/-- `(white black)^j`. -/
def wbPattern : Nat → List Bool
  | 0 => []
  | j + 1 => false :: true :: wbPattern j

theorem length_wbPattern : ∀ j, (wbPattern j).length = 2 * j
  | 0 => rfl
  | j + 1 => by simp [wbPattern, length_wbPattern j]; omega

/-- The driver after the black run: the block `u`, then nine black cells. -/
def drv (u : List Bool) : List Bool := u ++ List.replicate 9 true

theorem getD_replicate_black : ∀ i, i < 9 → (List.replicate 9 true).getD i false = true := by
  decide

theorem getD_drv_black : ∀ (u : List Bool) (i : Nat), u.length ≤ i → i < u.length + 9 →
    (drv u).getD i false = true
  | [], i, _, h => getD_replicate_black i (by simpa using h)
  | a :: u, i, h1, h2 => by
    cases i with
    | zero => simp at h1
    | succ i =>
      show (drv u).getD i false = true
      exact getD_drv_black u i (by simp at h1; omega) (by simp at h2; omega)

/-- The finite check: all rows with prefix `(white black)^j0` give the same column-1 trace. -/
def Determined (u : List Bool) (j0 : Nat) : Bool :=
  (allLists (u.length + 10 - 2 * j0)).all fun tail =>
    traceCol1 (drv u) (wbPattern j0 ++ tail) ==
      traceCol1 (drv u) (wbPattern j0 ++ List.replicate (u.length + 10 - 2 * j0) false)

theorem rowAt_split (t : Nat) : ∀ (a b : Nat) (p : Int), rowAt t p (a + b) = rowAt t p a ++ rowAt t (p + a) b
  | 0, b, p => by simp [rowAt]
  | a + 1, b, p => by
    rw [show a + 1 + b = (a + b) + 1 by omega]
    show cell t p :: rowAt t (p + 1) (a + b) = cell t p :: rowAt t (p + 1) a ++ rowAt t (p + ((a + 1 : Nat) : Int)) b
    rw [rowAt_split t a b (p + 1), show p + 1 + (a : Int) = p + ((a + 1 : Nat) : Int) by omega]
    rfl

theorem rowAt_wb (t : Nat) (p : Int) : ∀ j : Nat, (∀ i : Nat, 1 ≤ i → i ≤ j →
    cell t (p + 2 * (i : Int) - 2) = false ∧ cell t (p + 2 * (i : Int) - 1) = true) →
    rowAt t p (2 * j) = wbPattern j
  | 0, _ => rfl
  | j + 1, h => by
    have h1 := h 1 (by omega) (by omega)
    rw [show p + 2 * ((1 : Nat) : Int) - 2 = p by omega, show p + 2 * ((1 : Nat) : Int) - 1 = p + 1 by omega] at h1
    have ih := rowAt_wb t (p + 2) j (fun i hi1 hij => by
      have := h (i + 1) (by omega) (by omega)
      rw [show p + 2 * ((i + 1 : Nat) : Int) - 2 = p + 2 + 2 * (i : Int) - 2 by omega,
        show p + 2 * ((i + 1 : Nat) : Int) - 1 = p + 2 + 2 * (i : Int) - 1 by omega] at this
      exact this)
    show cell t p :: cell t (p + 1) :: rowAt t (p + 1 + 1) (2 * j) = false :: true :: wbPattern j
    rw [h1.1, h1.2, show p + 1 + 1 = p + 2 by omega, ih]

/-- **Theorem B′.** A black run of length `r ≥ max 9 (9 j0)` followed by a block `u` with
`Determined u j0` cannot be the repeating word of an eventually periodic center column. -/
theorem no_black_run_block (u : List Bool) (j0 : Nat) (hdet : Determined u j0 = true)
    (hj0 : 2 * j0 ≤ u.length + 10)
    (T r t1 : Nat) (hper : ∀ t, T ≤ t → center (t + (r + u.length)) = center t)
    (ht1 : T ≤ t1) (hr9 : 9 ≤ r) (hrj : 9 * j0 ≤ r)
    (hrun : ∀ s, s < r → center (t1 + s) = true)
    (hu : ∀ i, i < u.length → center (t1 + r + i) = u.getD i false) : False := by
  generalize hPdef : r + u.length = P at hper
  have hP : 0 < P := by omega
  have hperk : ∀ k t, T ≤ t → center (t + k * P) = center t := periodic_mul hper
  have hblack : ∀ k s, s < r → cell (t1 + k * P + s) 0 = true := by
    intro k s hs
    have := hperk k (t1 + s) (by omega)
    show center (t1 + k * P + s) = true
    rw [show t1 + k * P + s = t1 + s + k * P by omega, this]
    exact hrun s hs
  have hublock : ∀ k i, i < u.length → cell (t1 + r + k * P + i) 0 = u.getD i false := by
    intro k i hi
    have := hperk k (t1 + r + i) (by omega)
    show center (t1 + r + k * P + i) = _
    rw [show t1 + r + k * P + i = t1 + r + i + k * P by omega, this]
    exact hu i hi
  -- the drivers from e_k = t1 + r + k P: u, then nine black cells
  have hdrv : ∀ k i, i < (drv u).length → cell (t1 + r + k * P + i) 0 = (drv u).getD i false := by
    intro k i hi
    simp only [drv, List.length_append, List.length_replicate] at hi
    by_cases hiu : i < u.length
    · rw [hublock k i hiu]; simp [drv, List.getD_eq_getElem?_getD, List.getElem?_append_left hiu]
    · have hPk : (k + 1) * P = k * P + P := Nat.succ_mul k P
      have := hblack (k + 1) (i - u.length) (by omega)
      rw [hPk, show t1 + (k * P + P) + (i - u.length) = t1 + r + k * P + i by omega] at this
      rw [this, getD_drv_black u i (by omega) (by omega)]
  -- the row at e_k: (white black)^j0, then some tail
  have hrow : ∀ k, rowAt (t1 + r + k * P) 1 (2 * j0) = wbPattern j0 := by
    intro k
    apply rowAt_wb
    intro i hi1 hij
    have := black_shield 0 j0 (t1 + k * P + (r - 9 * j0)) (fun s hs => by
        have := hblack k (r - 9 * j0 + s) (by omega)
        rwa [show t1 + k * P + (r - 9 * j0 + s) = t1 + k * P + (r - 9 * j0) + s by omega] at this)
      i hi1 hij
    rw [show t1 + k * P + (r - 9 * j0) + 9 * j0 = t1 + r + k * P by omega] at this
    rw [show (1 : Int) + 2 * (i : Int) - 2 = 0 + 2 * (i : Int) - 1 by omega,
      show (1 : Int) + 2 * (i : Int) - 1 = 0 + 2 * (i : Int) by omega]
    exact this
  -- the column-1 trace from e_k does not depend on k
  have htrace : ∀ k, colTrace (t1 + r + k * P) (drv u).length =
      traceCol1 (drv u) (wbPattern j0 ++ List.replicate (u.length + 10 - 2 * j0) false) := by
    intro k
    rw [← traceCol1_rowAt (drv u) (t1 + r + k * P) (hdrv k)]
    have hlen : (drv u).length + 1 = 2 * j0 + (u.length + 10 - 2 * j0) := by
      simp [drv]; omega
    rw [hlen, rowAt_split, hrow k]
    have hmem : rowAt (t1 + r + k * P) (1 + ((2 * j0 : Nat) : Int)) (u.length + 10 - 2 * j0) ∈
        allLists (u.length + 10 - 2 * j0) := by
      have := mem_allLists (rowAt (t1 + r + k * P) (1 + ((2 * j0 : Nat) : Int)) (u.length + 10 - 2 * j0))
      rwa [length_rowAt] at this
    have := List.all_eq_true.mp hdet _ hmem
    simpa using this
  have hcol : ∀ k s, s < P → cell (t1 + r + s) 1 = cell (t1 + r + k * P + s) 1 := by
    intro k s hs
    by_cases hs1 : s < (drv u).length + 1
    · have a := congrArg (fun l => l.getD s false) (htrace 0)
      have b := congrArg (fun l => l.getD s false) (htrace k)
      simp only [Nat.zero_mul, Nat.add_zero] at a b
      rw [colTrace_getD _ _ _ (by omega)] at a b
      rw [a, b]
    · simp only [drv, List.length_append, List.length_replicate] at hs1
      have white1 : ∀ t', (∀ s', s' < 9 → cell (t' + s') 0 = true) → cell (t' + 9) 1 = false := by
        intro t' h
        have := (nine_black t' 0 h).1
        simpa using this
      have hPk : ∀ k', (k' + 1) * P = k' * P + P := fun k' => Nat.succ_mul k' P
      have wk : ∀ k', cell (t1 + r + k' * P + s) 1 = false := by
        intro k'
        have := white1 (t1 + r + k' * P + s - 9) (fun s' hs' => by
          have := hblack (k' + 1) (s - 9 + s' - u.length) (by omega)
          rwa [hPk, show t1 + (k' * P + P) + (s - 9 + s' - u.length) = t1 + r + k' * P + s - 9 + s' by
            omega] at this)
        rwa [show t1 + r + k' * P + s - 9 + 9 = t1 + r + k' * P + s by omega] at this
      have w0 := wk 0
      simp only [Nat.zero_mul, Nat.add_zero] at w0
      rw [w0, wk k]
  have h1 : EventuallyPeriodic (fun t => cell t (0 + 1)) := by
    refine ⟨t1 + r, P, hP, fun t ht => ?_⟩
    show cell (t + P) (0 + 1) = cell t (0 + 1)
    rw [show (0 : Int) + 1 = 1 by rfl]
    have hdm := Nat.div_add_mod (t - (t1 + r)) P
    generalize (t - (t1 + r)) / P = q at hdm
    have hmod := Nat.mod_lt (t - (t1 + r)) hP
    generalize (t - (t1 + r)) % P = s at hdm hmod
    have hq1 : (q + 1) * P = q * P + P := Nat.succ_mul q P
    have e1 := hcol q s hmod
    have e2 := hcol (q + 1) s hmod
    rw [hq1] at e2
    have hcomm : P * q = q * P := Nat.mul_comm P q
    rw [show t + P = t1 + r + (q * P + P) + s by omega, ← e2, e1,
      show t1 + r + q * P + s = t by omega]
  have h0 : EventuallyPeriodic (fun t => cell t 0) := ⟨T, P, hP, hper⟩
  exact not_adjacent 0 h0 h1

/-- Example: `1^r 0` for every `r ≥ 18`. -/
theorem det_0 : Determined [false] 2 = true := by decide +kernel

/-- Blocks of length ≤ 4 after a black run (start and end white), with `j0` (found by SAT, checked
here by the kernel). Theorem B′ then excludes `1^r u` for every `r ≥ max 9 (9 j0)`. -/
theorem det_00 : Determined [false, false] 2 = true := by decide +kernel
theorem det_000 : Determined [false, false, false] 2 = true := by decide +kernel
theorem det_010 : Determined [false, true, false] 3 = true := by decide +kernel
theorem det_0000 : Determined [false, false, false, false] 2 = true := by decide +kernel
theorem det_0010 : Determined [false, false, true, false] 3 = true := by decide +kernel
theorem det_0100 : Determined [false, true, false, false] 2 = true := by decide +kernel
theorem det_0110 : Determined [false, true, true, false] 3 = true := by decide +kernel

/-- Example instance: the center column is never eventually periodic with repeating word
`1^r 0`, `r ≥ 18`, whatever the transient. -/
theorem no_period_black_run_then_white (T r t1 : Nat) (hr : 18 ≤ r)
    (hper : ∀ t, T ≤ t → center (t + (r + 1)) = center t) (ht1 : T ≤ t1)
    (hrun : ∀ s, s < r → center (t1 + s) = true) (hw : center (t1 + r) = false) : False :=
  no_black_run_block [false] 2 det_0 (by decide) T r t1 hper ht1 (by omega) (by omega) hrun
    (fun i hi => by
      have : i = 0 := by simp at hi; omega
      subst this; simpa using hw)

/-! ### Theorem D: a black run of length ≥ 9 followed by a long white run -/

/-- During a white run of the center column, a black cell in column 1 stays black. -/
theorem black_stays (a n : Nat) (hc : ∀ i, i < n → cell (a + i) 0 = false) (h1 : cell a 1 = true) :
    ∀ i, i ≤ n → cell (a + i) 1 = true
  | 0, _ => by simpa using h1
  | i + 1, hi => by
    have ih := black_stays a n hc h1 i (by omega)
    show rule (cell (a + i) (1 - 1)) (cell (a + i) 1) (cell (a + i) (1 + 1)) = true
    rw [show (1 : Int) - 1 = 0 by rfl, hc i (by omega), ih]
    rfl

/-- **Theorem D.** If the center column is periodic with period `P` from `T` on, a period cannot
contain a black run of length `s ≥ 9` immediately followed by a white run of length `r` with
`r ≥ 1 + 9 ⌈(k + 8) / 2⌉`, where `k = P - s - r` is the length of the rest of the period. -/
theorem no_black_white_run (T P s r t1 : Nat) (hper : ∀ t, T ≤ t → center (t + P) = center t)
    (ht1 : T ≤ t1) (hs : 9 ≤ s) (hsr : s + r ≤ P)
    (hblk : ∀ i, i < s → center (t1 + i) = true)
    (hwht : ∀ i, i < r → center (t1 + s + i) = false)
    (hlong : 1 + 9 * ((P - s - r + 9) / 2) ≤ r) : False := by
  have hP : 0 < P := by omega
  have hj1 : P - s - r + 8 ≤ 2 * ((P - s - r + 9) / 2) := by omega
  generalize hjdef : (P - s - r + 9) / 2 = j at hj1 hlong
  have hperk : ∀ k t, T ≤ t → center (t + k * P) = center t := periodic_mul hper
  have hMul : ∀ k, (k + 1) * P = k * P + P := fun k => Nat.succ_mul k P
  have cblk : ∀ k i, i < s → cell (t1 + k * P + i) 0 = true := by
    intro k i hi
    have := hperk k (t1 + i) (by omega)
    show center (t1 + k * P + i) = true
    rw [show t1 + k * P + i = t1 + i + k * P by omega, this]; exact hblk i hi
  have cwht : ∀ k i, i < r → cell (t1 + s + k * P + i) 0 = false := by
    intro k i hi
    have := hperk k (t1 + s + i) (by omega)
    show center (t1 + s + k * P + i) = false
    rw [show t1 + s + k * P + i = t1 + s + i + k * P by omega, this]; exact hwht i hi
  -- start of the white run of period k: column 1 white, column 2 black (Lemma A)
  have hstart : ∀ k, cell (t1 + s + k * P) 1 = false ∧ cell (t1 + s + k * P) 2 = true := by
    intro k
    have := nine_black (t1 + k * P + (s - 9)) 0 (fun i hi => by
      have := cblk k (s - 9 + i) (by omega)
      rwa [show t1 + k * P + (s - 9 + i) = t1 + k * P + (s - 9) + i by omega] at this)
    rw [show t1 + k * P + (s - 9) + 9 = t1 + s + k * P by omega] at this
    simpa using this
  -- column 1 is black during the rest of the white run
  have hrun1 : ∀ k i, 1 ≤ i → i ≤ r → cell (t1 + s + k * P + i) 1 = true := by
    intro k i hi1 hir
    have c1 : cell (t1 + s + k * P + 1) 1 = true := by
      show rule (cell (t1 + s + k * P) (1 - 1)) (cell (t1 + s + k * P) 1)
        (cell (t1 + s + k * P) (1 + 1)) = true
      have h0 := cwht k 0 (by omega)
      rw [show t1 + s + k * P + 0 = t1 + s + k * P by omega] at h0
      rw [show (1 : Int) - 1 = 0 by rfl, show (1 : Int) + 1 = 2 by rfl, h0, (hstart k).1,
        (hstart k).2]
      rfl
    have := black_stays (t1 + s + k * P + 1) (r - 1) (fun i' hi' => by
      have := cwht k (1 + i') (by omega)
      rwa [show t1 + s + k * P + (1 + i') = t1 + s + k * P + 1 + i' by omega] at this) c1
      (i - 1) (by omega)
    rwa [show t1 + s + k * P + 1 + (i - 1) = t1 + s + k * P + i by omega] at this
  -- at the end of the white run: column 1 black, columns 2..2j+1 read (white black)^j
  have hend : ∀ k i, 1 ≤ i → i ≤ j →
      cell (t1 + s + r + k * P) (1 + 2 * (i : Int) - 1) = false ∧
        cell (t1 + s + r + k * P) (1 + 2 * (i : Int)) = true := by
    intro k i hi1 hij
    have := black_shield 1 j (t1 + s + k * P + (r - 9 * j)) (fun i' hi' => by
        have := hrun1 k (r - 9 * j + i') (by omega) (by omega)
        rwa [show t1 + s + k * P + (r - 9 * j + i') = t1 + s + k * P + (r - 9 * j) + i' by omega]
          at this) i hi1 hij
    rwa [show t1 + s + k * P + (r - 9 * j) + 9 * j = t1 + s + r + k * P by omega] at this
  have hrowagree : ∀ k, ∀ p : Int, 1 ≤ p → p ≤ ((2 * j + 1 : Nat) : Int) →
      cell (t1 + s + r) p = cell (t1 + s + r + k * P) p := by
    intro k p hp1 hp2
    by_cases hp : p = 1
    · subst hp
      have a := hrun1 0 r (by omega) (Nat.le_refl r)
      have b := hrun1 k r (by omega) (Nat.le_refl r)
      simp only [Nat.zero_mul, Nat.add_zero] at a
      rw [show t1 + s + k * P + r = t1 + s + r + k * P by omega] at b
      rw [a, b]
    have a0 := hend 0
    simp only [Nat.zero_mul, Nat.add_zero] at a0
    by_cases hpar : p % 2 = 0
    · have hi : p = 1 + 2 * ((((p) / 2).toNat : Nat) : Int) - 1 := by omega
      rw [hi, (a0 _ (by omega) (by omega)).1, (hend k _ (by omega) (by omega)).1]
    · have hi : p = 1 + 2 * ((((p - 1) / 2).toNat : Nat) : Int) := by omega
      rw [hi, (a0 _ (by omega) (by omega)).2, (hend k _ (by omega) (by omega)).2]
  have hdrv : ∀ k s', cell (t1 + s + r + s') 0 = cell (t1 + s + r + k * P + s') 0 := by
    intro k s'
    have := hperk k (t1 + s + r + s') (by omega)
    show center (t1 + s + r + s') = center (t1 + s + r + k * P + s')
    rw [show t1 + s + r + k * P + s' = t1 + s + r + s' + k * P by omega, this]
  have white1 : ∀ t', (∀ s', s' < 9 → cell (t' + s') 0 = true) → cell (t' + 9) 1 = false := by
    intro t' h
    have := (nine_black t' 0 h).1
    simpa using this
  -- column 1 over one period starting at the white run: independent of the period index
  have hcol : ∀ k i, i < P → cell (t1 + s + i) 1 = cell (t1 + s + k * P + i) 1 := by
    intro k i hi
    by_cases hi0 : i = 0
    · subst hi0
      have a := (hstart 0).1
      simp only [Nat.zero_mul, Nat.add_zero] at a
      simp only [Nat.add_zero]
      rw [a, (hstart k).1]
    by_cases hir : i ≤ r
    · have a := hrun1 0 i (by omega) hir
      simp only [Nat.zero_mul, Nat.add_zero] at a
      rw [a, hrun1 k i (by omega) hir]
    by_cases hic : i ≤ r + 2 * j
    · have := cone_agree (t1 + s + r) (t1 + s + r + k * P) (2 * j + 1) (hdrv k) (hrowagree k)
        (i - r) 1 (by omega) (by omega)
      rwa [show t1 + s + r + (i - r) = t1 + s + i by omega,
        show t1 + s + r + k * P + (i - r) = t1 + s + k * P + i by omega] at this
    · -- at least nine steps into the next black run
      have wk : ∀ k', cell (t1 + s + k' * P + i) 1 = false := by
        intro k'
        have := white1 (t1 + s + k' * P + i - 9) (fun s' hs' => by
          have := cblk (k' + 1) (s + i - 9 + s' - P) (by omega)
          rwa [hMul k', show t1 + (k' * P + P) + (s + i - 9 + s' - P) =
            t1 + s + k' * P + i - 9 + s' by omega] at this)
        rwa [show t1 + s + k' * P + i - 9 + 9 = t1 + s + k' * P + i by omega] at this
      have w0 := wk 0
      simp only [Nat.zero_mul, Nat.add_zero] at w0
      rw [w0, wk k]
  have h1 : EventuallyPeriodic (fun t => cell t (0 + 1)) := by
    refine ⟨t1 + s, P, hP, fun t ht => ?_⟩
    show cell (t + P) (0 + 1) = cell t (0 + 1)
    rw [show (0 : Int) + 1 = 1 by rfl]
    have hdm := Nat.div_add_mod (t - (t1 + s)) P
    generalize (t - (t1 + s)) / P = q at hdm
    have hmod := Nat.mod_lt (t - (t1 + s)) hP
    generalize (t - (t1 + s)) % P = i at hdm hmod
    have hq1 : (q + 1) * P = q * P + P := Nat.succ_mul q P
    have hcomm : P * q = q * P := Nat.mul_comm P q
    have e1 := hcol q i hmod
    have e2 := hcol (q + 1) i hmod
    rw [hq1] at e2
    rw [show t + P = t1 + s + (q * P + P) + i by omega, ← e2, e1,
      show t1 + s + q * P + i = t by omega]
  have h0 : EventuallyPeriodic (fun t => cell t 0) := ⟨T, P, hP, hper⟩
  exact not_adjacent 0 h0 h1

end AbsorbRight

#print axioms AbsorbRight.no_black_run_block
#print axioms AbsorbRight.no_period_black_run_then_white
