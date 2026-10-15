import Ruliology.CellularAutomata.Rule30Jen

/-!
# Jen's hypotheses do not decide Problem 1 (scratch)

Consider the elementary CA `new = left xor g(center, right)` from a single black cell, for any
`g` with `g 0 0 = 0` and `g 0 1 = 1`. Rule 30 is `g = or`. Every such rule is left-permutive
and has a left edge moving one cell per step, and Jen's adjacent-column argument goes through
verbatim (`not_adjacent`): no two adjacent columns are both eventually periodic.

But for `g = fun _ r => r` (rule 90), `g = xor` (rule 150) and `g = fun c r => !c && r`
(rule 210, nonlinear, not right-permutive, not mirror-symmetric, like rule 30) the center column
is eventually constant (`center90`, `center150`, `center210`). So left-permutivity, the left
edge and Jen's theorem cannot by themselves imply Problem 1, not even its period-1 case: a proof
must use something specific to `or`. (For rule 30 the period-1 case uses that `or` is monotone.)
-/

namespace R30Barrier
open Ruliology.CellularAutomata.Rule30Jen (EventuallyPeriodic common_period)

/-- The rule `left xor g(center, right)` from a single black cell at `0`. -/
def run (g : Bool → Bool → Bool) : Nat → Int → Bool
  | 0, p => decide (p = 0)
  | t + 1, p => xor (run g t (p - 1)) (g (run g t p) (run g t (p + 1)))

section general
variable (g : Bool → Bool → Bool) (g00 : g false false = false) (g01 : g false true = true)
include g00

theorem run_eq_false_of_lt : ∀ (t : Nat) (p : Int), p < -(t : Int) → run g t p = false
  | 0, p, h => by simp [run]; omega
  | t + 1, p, h => by
    show xor (run g t (p - 1)) (g (run g t p) (run g t (p + 1))) = false
    rw [run_eq_false_of_lt t (p - 1) (by omega), run_eq_false_of_lt t p (by omega),
      run_eq_false_of_lt t (p + 1) (by omega), g00]
    rfl

include g01 in
theorem run_left_edge : ∀ t : Nat, run g t (-(t : Int)) = true
  | 0 => rfl
  | t + 1 => by
    show xor (run g t (-((t + 1 : Nat) : Int) - 1)) (g (run g t (-((t + 1 : Nat) : Int)))
      (run g t (-((t + 1 : Nat) : Int) + 1))) = true
    rw [run_eq_false_of_lt g g00 t _ (by omega), run_eq_false_of_lt g g00 t _ (by omega),
      show -((t + 1 : Nat) : Int) + 1 = -(t : Int) by omega, run_left_edge t, g01]
    rfl

omit g00 in
theorem run_left (t : Nat) (i : Int) :
    run g t (i - 1) = xor (run g (t + 1) i) (g (run g t i) (run g t (i + 1))) := by
  show run g t (i - 1) = xor (xor (run g t (i - 1)) (g (run g t i) (run g t (i + 1))))
    (g (run g t i) (run g t (i + 1)))
  cases run g t (i - 1) <;> cases g (run g t i) (run g t (i + 1)) <;> rfl

omit g00 in
theorem periodic_left {T P : Nat} {i : Int}
    (h0 : ∀ t, T ≤ t → run g (t + P) i = run g t i)
    (h1 : ∀ t, T ≤ t → run g (t + P) (i + 1) = run g t (i + 1)) :
    ∀ t, T ≤ t → run g (t + P) (i - 1) = run g t (i - 1) := by
  intro t ht
  rw [run_left, run_left g t, show t + P + 1 = (t + 1) + P by omega, h0 (t + 1) (by omega),
    h0 t ht, h1 t ht]

omit g00 in
theorem periodic_left_all {T P : Nat} {i : Int}
    (h0 : ∀ t, T ≤ t → run g (t + P) i = run g t i)
    (h1 : ∀ t, T ≤ t → run g (t + P) (i + 1) = run g t (i + 1)) :
    ∀ m : Nat, (∀ t, T ≤ t → run g (t + P) (i - m) = run g t (i - m)) ∧
      ∀ t, T ≤ t → run g (t + P) (i - m + 1) = run g t (i - m + 1) := by
  intro m
  induction m with
  | zero => simpa using ⟨h0, h1⟩
  | succ m ih =>
    refine ⟨?_, ?_⟩
    · have := periodic_left g ih.1 ih.2
      rwa [show i - (m : Int) - 1 = i - ((m + 1 : Nat) : Int) by omega] at this
    · rw [show i - ((m + 1 : Nat) : Int) + 1 = i - (m : Int) by omega]
      exact ih.1

include g01 in
theorem no_left_periodic {T P : Nat} (hP : 0 < P) {i : Int}
    (h : ∀ m : Nat, ∀ t, T ≤ t → run g (t + P) (i - m) = run g t (i - m)) : False := by
  let q : Int := min i (-((T + P : Nat) : Int) - 1)
  have hq : q ≤ i := Int.min_le_left _ _
  have hq' : q ≤ -((T + P : Nat) : Int) - 1 := Int.min_le_right _ _
  obtain ⟨t₁, ht₁⟩ : ∃ t₁ : Nat, (t₁ : Int) = -q := ⟨(-q).toNat, by omega⟩
  have hper := h (i - q).toNat (t₁ - P) (by omega)
  rw [show i - (((i - q).toNat : Nat) : Int) = q by omega, show t₁ - P + P = t₁ by omega] at hper
  have hedge : run g t₁ q = true := by
    have := run_left_edge g g00 g01 t₁
    rwa [show -(t₁ : Int) = q by omega] at this
  have hwhite : run g (t₁ - P) q = false := run_eq_false_of_lt g g00 _ _ (by omega)
  rw [hedge, hwhite] at hper
  exact absurd hper (by decide)

include g01 in
/-- **Jen's adjacent-column theorem for every rule `left xor g(center, right)`** with
`g 0 0 = 0`, `g 0 1 = 1`. -/
theorem not_adjacent (i : Int) (h0 : EventuallyPeriodic fun t => run g t i)
    (h1 : EventuallyPeriodic fun t => run g t (i + 1)) : False := by
  obtain ⟨T, P, hP, hp0, hp1⟩ := common_period h0 h1
  exact no_left_periodic g g00 g01 hP fun m => (periodic_left_all g hp0 hp1 m).1

end general

/-! ### Rules 90, 150 and 210: the center column is eventually constant -/

/-- Mirror symmetry of a symmetric rule from the symmetric seed. -/
theorem run_symm (g : Bool → Bool → Bool) (hs : ∀ a b c, xor a (g b c) = xor c (g b a)) :
    ∀ t p, run g t (-p) = run g t p
  | 0, p => by simp only [run]; by_cases h : p = 0 <;> simp [h]
  | t + 1, p => by
    show xor (run g t (-p - 1)) (g (run g t (-p)) (run g t (-p + 1))) =
      xor (run g t (p - 1)) (g (run g t p) (run g t (p + 1)))
    rw [show -p - 1 = -(p + 1) by omega, show -p + 1 = -(p - 1) by omega, run_symm g hs t (p + 1),
      run_symm g hs t p, run_symm g hs t (p - 1), hs]

/-- Rule 90: `left xor right`. -/
def g90 (_ r : Bool) : Bool := r
/-- Rule 150: `left xor center xor right`. -/
def g150 (c r : Bool) : Bool := xor c r
/-- Rule 210: `left xor (not center and right)`. -/
def g210 (c r : Bool) : Bool := !c && r
/-- Rule 30: `left xor (center or right)`. -/
def g30 (c r : Bool) : Bool := c || r

theorem run30_eq_cell : ∀ t p, run g30 t p = Ruliology.CellularAutomata.Rule30Jen.cell t p
  | 0, _ => rfl
  | t + 1, p => by
    show xor (run g30 t (p - 1)) (g30 (run g30 t p) (run g30 t (p + 1))) = _
    rw [run30_eq_cell t (p - 1), run30_eq_cell t p, run30_eq_cell t (p + 1)]
    rfl

/-- **Rule 90**: the center column is `1, 0, 0, 0, …`. -/
theorem center90 (t : Nat) : run g90 (t + 1) 0 = false := by
  show xor (run g90 t (0 - 1)) (g90 (run g90 t 0) (run g90 t (0 + 1))) = false
  have hs := run_symm g90 (by intro a b c; cases a <;> cases c <;> rfl) t 1
  rw [show (0 : Int) - 1 = -1 by rfl, hs]
  simp [g90]

/-- **Rule 150**: the center column is constantly `1`. -/
theorem center150 : ∀ t, run g150 t 0 = true
  | 0 => rfl
  | t + 1 => by
    show xor (run g150 t (0 - 1)) (g150 (run g150 t 0) (run g150 t (0 + 1))) = true
    have hs := run_symm g150 (by intro a b c; cases a <;> cases b <;> cases c <;> rfl) t 1
    rw [show (0 : Int) - 1 = -1 by rfl, show (0 : Int) + 1 = 1 by rfl, hs, center150 t]
    cases run g150 t 1 <;> rfl

/-- From the single seed, rule 210 draws exactly rule 90's pattern, which lives on the cells
with `t + p` even (where the center cell is always white when it matters). -/
theorem run210_eq : ∀ t p, run g210 t p = run g90 t p ∧
    (run g90 t p = true → ((t : Int) + p) % 2 = 0)
  | 0, p => by
    refine ⟨rfl, fun h => ?_⟩
    simp [run] at h; subst h; rfl
  | t + 1, p => by
    have ih := run210_eq t
    refine ⟨?_, fun h => ?_⟩
    · show xor (run g210 t (p - 1)) (g210 (run g210 t p) (run g210 t (p + 1))) =
        xor (run g90 t (p - 1)) (g90 (run g90 t p) (run g90 t (p + 1)))
      rw [(ih (p - 1)).1, (ih p).1, (ih (p + 1)).1]
      by_cases hpar : ((t : Int) + p) % 2 = 0
      · -- neighbours have odd parity, so they are white
        have hl : run g90 t (p - 1) = false := by
          cases e : run g90 t (p - 1)
          · rfl
          · have := (ih (p - 1)).2 e; omega
        have hr : run g90 t (p + 1) = false := by
          cases e : run g90 t (p + 1)
          · rfl
          · have := (ih (p + 1)).2 e; omega
        rw [hl, hr]; simp [g210, g90]
      · -- the center has odd parity, so it is white
        have hc : run g90 t p = false := by
          cases e : run g90 t p
          · rfl
          · have := (ih p).2 e; omega
        rw [hc]; simp [g210, g90]
    · have h' : xor (run g90 t (p - 1)) (g90 (run g90 t p) (run g90 t (p + 1))) = true := h
      simp only [g90] at h'
      cases e1 : run g90 t (p - 1) <;> cases e2 : run g90 t (p + 1) <;> rw [e1, e2] at h' <;>
        simp at h'
      · have := (ih (p + 1)).2 e2; omega
      · have := (ih (p - 1)).2 e1; omega

/-- **Rule 210**: the center column is `1, 0, 0, 0, …`. -/
theorem center210 (t : Nat) : run g210 (t + 1) 0 = false := by
  rw [(run210_eq (t + 1) 0).1]; exact center90 t

/-- **Barrier.** Rules 90, 150, 210 satisfy the hypotheses of the generalized Jen theorem
(`not_adjacent` applies to them) and yet their center columns are eventually periodic. -/
theorem barrier :
    (∀ i, ¬ ((EventuallyPeriodic fun t => run g210 t i) ∧
      EventuallyPeriodic fun t => run g210 t (i + 1))) ∧
    (EventuallyPeriodic fun t => run g90 t 0) ∧ (EventuallyPeriodic fun t => run g150 t 0) ∧
    (EventuallyPeriodic fun t => run g210 t 0) := by
  refine ⟨fun i h => not_adjacent g210 rfl rfl i h.1 h.2, ⟨1, 1, by decide, fun t ht => ?_⟩,
    ⟨0, 1, by decide, fun t _ => by
      show run g150 (t + 1) 0 = run g150 t 0
      rw [center150, center150]⟩, ⟨1, 1, by decide, fun t ht => ?_⟩⟩
  · obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
    show run g90 (s + 1 + 1) 0 = run g90 (s + 1) 0
    rw [center90, center90]
  · obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
    show run g210 (s + 1 + 1) 0 = run g210 (s + 1) 0
    rw [center210, center210]

end R30Barrier
