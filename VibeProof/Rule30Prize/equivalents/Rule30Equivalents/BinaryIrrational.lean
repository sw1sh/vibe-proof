import Rule30Equivalents.Basic
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.LinearCombination

/-!
# Problem 1 as the irrationality of a real number

Read the center column `c(0), c(1), c(2), …` of rule 30 as the digits after the point of a binary
number, `centerBinary = 0.c(0) c(1) c(2) …₂ = ∑ₜ c(t) / 2^(t+1)` (with `true = 1`, `false = 0`).
**Problem 1 holds iff this number is irrational.** The same is true in every base `B ≥ 2`: for
example Problem 1 holds iff the decimal number `0.c(0) c(1) c(2) …₁₀`, whose digits are all `0`
or `1`, is irrational.

## Statements

* `eventuallyPeriodic_iff_not_irrational`: for every `b : ℕ → Bool` and every natural `B ≥ 2`,
  `EventuallyPeriodic b ↔ ¬ Irrational (∑' t, (if b t then 1 else 0) / B ^ (t + 1))`;
  `irrational_iff_not_eventuallyPeriodic` is the contrapositive.
* `problem1_iff_irrational_base`: `Problem1` iff `0.c(0) c(1) c(2) …` in base `B` is irrational.
* `problem1_iff_irrational_binary`: `Problem1 ↔ Irrational centerBinary` (base 2).
* `problem1_iff_irrational_decimal`: `Problem1 ↔ Irrational centerDecimal` (base 10).

## Proof

Let `x_t = ∑' s, b(t + s) / B^(s+1)` be the value of the tail from position `t`
(`baseValue B (tail b t)`). Comparison with `∑ 1/2^(s+1) = 1` gives `0 ≤ x_t ≤ 1`. Splitting off
the first term gives `B x_t = b(t) + x_(t+1)` (`mul_baseValue`), and so `B^t x_0 = N_t + x_t`, where
`N_t` is the natural number with base-`B` digits `b(0) … b(t-1)` (`pow_mul_baseValue`).

* (→) If `b(t + P) = b(t)` for `t ≥ T`, the tail from `T` is purely periodic, so `x_(T+P) = x_T`
  and `B^P x_T = N' + x_T` for a natural number `N'`. This is the geometric series:
  `x_T = N' / (B^P - 1)`. Then `x_0 = (N_T + x_T) / B^T` is rational.
* (←) If `x_0 = p/q`, then `q x_t = B^t p - q N_t` is an integer in `[0, q]`. So the tails take
  finitely many values, and `x_i = x_j` for some `i < j` by pigeonhole. If only finitely many
  digits are `1`, `b` is eventually `0`, hence eventually periodic. Otherwise every `x_t` is
  positive, so `b(t) = 1` iff `B x_t > 1` (`digit_iff`): a `1` gives `B x_t = 1 + x_(t+1) > 1`, a
  `0` gives `B x_t = x_(t+1) ≤ 1`. The tail value thus determines the next digit and, through
  `x_(t+1) = B x_t - b(t)`, the next tail value. By induction `x_(i+k) = x_(j+k)` and
  `b(i+k) = b(j+k)` for all `k`, so `b` has period `j - i` from `i` on.

The case split takes care of double expansions. In base 2, `0.0111…₂ = 0.1000…₂`: equal tail
values need not have equal digits. That only happens for eventually constant sequences, and when
infinitely many digits are `1` the tail value does determine the digit. For `B ≥ 3` the digits
`0, 1` never reach `B - 1`, and the expansion is always unique.

## Source

The classical theorem that a real number is rational iff its expansion in an integer base is
eventually periodic. For decimal fractions it goes back to J. Wallis, *A Treatise of Algebra*
(1685), J. H. Lambert and L. Euler in the eighteenth century, and C. F. Gauss, *Disquisitiones
Arithmeticae* (1801), art. 312 ff.; see L. E. Dickson, *History of the Theory of Numbers*, vol. I
(1919), ch. VI. A textbook treatment for an arbitrary base is G. H. Hardy and E. M. Wright,
*An Introduction to the Theory of Numbers* (1938), ch. IX.
-/

namespace Rule30Equivalents.BinaryIrrational

open Ruliology.CellularAutomata

/-- The real number `0.b(0) b(1) b(2) …` written in base `B`, with digit `1` for `true` and `0`
for `false`. -/
noncomputable def baseValue (B : ℕ) (b : ℕ → Bool) : ℝ :=
  ∑' t, (if b t then (1 : ℝ) else 0) / (B : ℝ) ^ (t + 1)

/-- The tail `b(t), b(t + 1), …` of a sequence. -/
def tail (b : ℕ → Bool) (t : ℕ) : ℕ → Bool := fun s => b (s + t)

/-- The first `t` digits `b(0) … b(t - 1)` read as a base-`B` numeral. -/
def lead (B : ℕ) (b : ℕ → Bool) : ℕ → ℕ
  | 0 => 0
  | t + 1 => B * lead B b t + (if b t then 1 else 0)

/-- The first digit of the tail from `t` is `b t`. -/
theorem tail_zero_apply (b : ℕ → Bool) (t : ℕ) : tail b t 0 = b t := by
  simp [tail]

/-- Dropping one more digit from the tail from `t` gives the tail from `t + 1`. -/
theorem tail_tail_one (b : ℕ → Bool) (t : ℕ) : tail (tail b t) 1 = tail b (t + 1) := by
  funext s
  simp only [tail]
  congr 1
  omega

section
variable {B : ℕ} (hB : 2 ≤ B)
include hB

/-- The base, as a real number, is at least `2`. -/
theorem two_le_cast : (2 : ℝ) ≤ B := by exact_mod_cast hB

/-- Each term `b(t) / B^(t+1)` is nonnegative. -/
theorem term_nonneg (b : ℕ → Bool) (t : ℕ) :
    0 ≤ (if b t then (1 : ℝ) else 0) / (B : ℝ) ^ (t + 1) := by
  split_ifs <;> positivity

/-- Each term is at most `1 / 2^(t+1)`, written `1 / 2 / 2^t` to match `tsum_geometric_two'`. -/
theorem term_le (b : ℕ → Bool) (t : ℕ) :
    (if b t then (1 : ℝ) else 0) / (B : ℝ) ^ (t + 1) ≤ 1 / 2 / 2 ^ t := by
  have hpow : (2 : ℝ) ^ (t + 1) ≤ (B : ℝ) ^ (t + 1) :=
    pow_le_pow_left₀ (by norm_num) (two_le_cast hB) _
  rw [div_div, ← pow_succ']
  split_ifs
  · exact one_div_le_one_div_of_le (by positivity) hpow
  · rw [zero_div]; positivity

/-- The series defining `baseValue B b` converges. -/
theorem summable_term (b : ℕ → Bool) :
    Summable (fun t => (if b t then (1 : ℝ) else 0) / (B : ℝ) ^ (t + 1)) :=
  Summable.of_nonneg_of_le (term_nonneg hB b) (term_le hB b) (summable_geometric_two' 1)

/-- `0 ≤ 0.b(0) b(1) …`. -/
theorem baseValue_nonneg (b : ℕ → Bool) : 0 ≤ baseValue B b :=
  tsum_nonneg (term_nonneg hB b)

/-- `0.b(0) b(1) … ≤ 1`, by comparison with `∑ 1/2^(t+1) = 1`. -/
theorem baseValue_le_one (b : ℕ → Bool) : baseValue B b ≤ 1 :=
  calc baseValue B b ≤ ∑' t : ℕ, (1 : ℝ) / 2 / 2 ^ t :=
        (summable_term hB b).tsum_le_tsum (term_le hB b) (summable_geometric_two' 1)
    _ = 1 := tsum_geometric_two' 1

/-- A single digit `1` makes the value positive. -/
theorem baseValue_pos (b : ℕ → Bool) {s : ℕ} (hs : b s = true) : 0 < baseValue B b := by
  refine (summable_term hB b).tsum_pos (term_nonneg hB b) s ?_
  have : (0 : ℝ) < B := by linarith [two_le_cast hB]
  simp only [hs, if_true]
  positivity

/-- Peeling off the first digit: `B · 0.b₀b₁b₂… = b₀ + 0.b₁b₂…`. -/
theorem mul_baseValue (b : ℕ → Bool) :
    (B : ℝ) * baseValue B b = (if b 0 then 1 else 0) + baseValue B (tail b 1) := by
  have hB0 : (B : ℝ) ≠ 0 := by linarith [two_le_cast hB]
  have e : baseValue B (tail b 1) =
      ∑' n, (if b (n + 1) then (1 : ℝ) else 0) / (B : ℝ) ^ (n + 1) := rfl
  rw [e, baseValue, (summable_term hB b).tsum_eq_zero_add]
  have h : ∀ n : ℕ, (if b (n + 1) then (1 : ℝ) else 0) / (B : ℝ) ^ (n + 1 + 1) =
      (B : ℝ)⁻¹ * ((if b (n + 1) then (1 : ℝ) else 0) / (B : ℝ) ^ (n + 1)) := by
    intro n
    rw [pow_succ]
    ring
  simp only [h, tsum_mul_left]
  field_simp
  ring

/-- Shifting by `t` digits: `B^t · 0.b₀b₁… = (b₀ … b_{t-1})_B + 0.b_t b_{t+1}…`. -/
theorem pow_mul_baseValue (b : ℕ → Bool) (t : ℕ) :
    (B : ℝ) ^ t * baseValue B b = lead B b t + baseValue B (tail b t) := by
  induction t with
  | zero => simp only [pow_zero, one_mul, lead, Nat.cast_zero, zero_add]; rfl
  | succ t ih =>
    have h1 := mul_baseValue hB (tail b t)
    rw [tail_tail_one, tail_zero_apply] at h1
    rw [pow_succ, mul_comm ((B : ℝ) ^ t) B, mul_assoc, ih, mul_add, h1]
    simp only [lead]
    push_cast
    ring

/-- One step of the digit dynamics: `x_{t+1} = B x_t - b(t)`. -/
theorem baseValue_tail_succ (b : ℕ → Bool) (t : ℕ) :
    baseValue B (tail b (t + 1)) = B * baseValue B (tail b t) - (if b t then 1 else 0) := by
  have h1 := mul_baseValue hB (tail b t)
  rw [tail_tail_one, tail_zero_apply] at h1
  linarith

/-- If infinitely many digits are `1`, the digit `b t` is read off the tail value. -/
theorem digit_iff (b : ℕ → Bool) (hinf : ∀ T, ∃ s, T ≤ s ∧ b s = true) (t : ℕ) :
    b t = true ↔ 1 < (B : ℝ) * baseValue B (tail b t) := by
  have h1 := mul_baseValue hB (tail b t)
  rw [tail_tail_one, tail_zero_apply] at h1
  rw [h1]
  obtain ⟨s, hs, hbs⟩ := hinf (t + 1)
  have hpos : 0 < baseValue B (tail b (t + 1)) := by
    refine baseValue_pos hB (tail b (t + 1)) (s := s - (t + 1)) ?_
    simp only [tail]
    rw [Nat.sub_add_cancel hs]
    exact hbs
  have hle := baseValue_le_one hB (tail b (t + 1))
  cases b t <;> simp <;> linarith

/-- (→): an eventually periodic digit sequence has a rational value (geometric series). -/
theorem not_irrational_of_eventuallyPeriodic (b : ℕ → Bool) (h : EventuallyPeriodic b) :
    ¬ Irrational (baseValue B b) := by
  obtain ⟨T, P, hP, hper⟩ := h
  have htail : tail (tail b T) P = tail b T := by
    funext s
    simp only [tail]
    rw [show s + P + T = s + T + P by omega]
    exact hper (s + T) (by omega)
  have e1 := pow_mul_baseValue hB (tail b T) P
  rw [htail] at e1
  have e2 := pow_mul_baseValue hB b T
  have hBP : (1 : ℝ) < (B : ℝ) ^ P := one_lt_pow₀ (by linarith [two_le_cast hB]) hP.ne'
  have hBT : (0 : ℝ) < (B : ℝ) ^ T := by
    have : (0 : ℝ) < B := by linarith [two_le_cast hB]
    positivity
  have hx : baseValue B (tail b T) = (lead B (tail b T) P : ℝ) / ((B : ℝ) ^ P - 1) := by
    rw [eq_div_iff (by linarith)]
    linarith
  have hv : baseValue B b = ((lead B b T : ℝ) + baseValue B (tail b T)) / (B : ℝ) ^ T := by
    rw [eq_div_iff hBT.ne']
    linarith
  rw [hv, hx]
  have : ((lead B b T : ℝ) + (lead B (tail b T) P : ℝ) / ((B : ℝ) ^ P - 1)) / (B : ℝ) ^ T =
      (((lead B b T : ℚ) + (lead B (tail b T) P : ℚ) / ((B : ℚ) ^ P - 1)) / (B : ℚ) ^ T : ℚ) := by
    push_cast
    ring
  rw [this]
  exact Rat.not_irrational _

/-- (←): a rational value forces an eventually periodic digit sequence (pigeonhole on the tails). -/
theorem eventuallyPeriodic_of_not_irrational (b : ℕ → Bool) (h : ¬ Irrational (baseValue B b)) :
    EventuallyPeriodic b := by
  by_cases hfin : ∃ T, ∀ t, T ≤ t → b t = false
  · obtain ⟨T, hT⟩ := hfin
    exact ⟨T, 1, Nat.one_pos, fun t ht => by rw [hT t ht, hT (t + 1) (by omega)]⟩
  have hinf : ∀ T, ∃ s, T ≤ s ∧ b s = true := by
    intro T
    by_contra hT
    exact hfin ⟨T, fun t ht => by
      cases hbt : b t
      · rfl
      · exact absurd ⟨t, ht, hbt⟩ hT⟩
  obtain ⟨r, hr⟩ := exists_rat_of_not_irrational h
  have hq : (0 : ℝ) < r.den := by exact_mod_cast r.den_pos
  have hrq : (r.den : ℝ) * baseValue B b = r.num := by
    rw [hr]
    exact_mod_cast r.den_mul_eq_num
  let m : ℕ → ℤ := fun t => (B : ℤ) ^ t * r.num - (r.den : ℤ) * lead B b t
  have hm : ∀ t, (m t : ℝ) = r.den * baseValue B (tail b t) := by
    intro t
    have e := pow_mul_baseValue hB b t
    simp only [m]
    push_cast
    linear_combination (r.den : ℝ) * e - (B : ℝ) ^ t * hrq
  have hmem : ∀ t, m t ∈ Set.Icc (0 : ℤ) r.den := by
    intro t
    have h0 := baseValue_nonneg hB (tail b t)
    have h1 := baseValue_le_one hB (tail b t)
    constructor
    · have : (0 : ℝ) ≤ m t := by rw [hm]; positivity
      exact_mod_cast this
    · have : (m t : ℝ) ≤ r.den := by rw [hm]; nlinarith
      exact_mod_cast this
  obtain ⟨i, j, hij, hmij⟩ := (Set.finite_Icc (0 : ℤ) r.den).exists_lt_map_eq_of_forall_mem hmem
  have hxij : baseValue B (tail b i) = baseValue B (tail b j) := by
    have := congrArg (fun z : ℤ => (z : ℝ)) hmij
    simp only [hm] at this
    exact mul_left_cancel₀ hq.ne' this
  have hdig := digit_iff hB b hinf
  have hk : ∀ k, baseValue B (tail b (i + k)) = baseValue B (tail b (j + k)) := by
    intro k
    induction k with
    | zero => simpa using hxij
    | succ k ih =>
      have hbk : b (i + k) = b (j + k) := by
        rw [Bool.eq_iff_iff, hdig, hdig, ih]
      rw [← add_assoc, ← add_assoc, baseValue_tail_succ hB, baseValue_tail_succ hB, ih, hbk]
  refine ⟨i, j - i, by omega, fun t ht => ?_⟩
  have e1 : t + (j - i) = j + (t - i) := by omega
  have e2 : t = i + (t - i) := by omega
  rw [e1, Bool.eq_iff_iff, hdig, hdig, ← hk (t - i), ← e2]

end

/-- **Rational digit sequences are exactly the eventually periodic ones.** For every base
`B ≥ 2`, a `0/1` digit sequence `b` is eventually periodic iff `0.b(0) b(1) b(2) …` in base `B` is
rational. -/
theorem eventuallyPeriodic_iff_not_irrational {B : ℕ} (hB : 2 ≤ B) (b : ℕ → Bool) :
    EventuallyPeriodic b ↔
      ¬ Irrational (∑' t, (if b t then (1 : ℝ) else 0) / (B : ℝ) ^ (t + 1)) :=
  ⟨not_irrational_of_eventuallyPeriodic hB b, eventuallyPeriodic_of_not_irrational hB b⟩

/-- The contrapositive: the base-`B` number `0.b(0) b(1) b(2) …` is irrational iff `b` is not
eventually periodic. -/
theorem irrational_iff_not_eventuallyPeriodic {B : ℕ} (hB : 2 ≤ B) (b : ℕ → Bool) :
    Irrational (∑' t, (if b t then (1 : ℝ) else 0) / (B : ℝ) ^ (t + 1)) ↔
      ¬ EventuallyPeriodic b := by
  rw [eventuallyPeriodic_iff_not_irrational hB, not_not]

/-- **Problem 1 in base `B`**: for every `B ≥ 2`, the center column is not eventually periodic iff
the base-`B` number `0.c(0) c(1) c(2) …` is irrational. -/
theorem problem1_iff_irrational_base {B : ℕ} (hB : 2 ≤ B) :
    Rule30Prize.Problem1 ↔ Irrational (∑' t, (if c t then (1 : ℝ) else 0) / (B : ℝ) ^ (t + 1)) := by
  rw [problem1_iff_not_eventuallyPeriodic, eventuallyPeriodic_iff_not_irrational hB, not_not]

/-- The center column of rule 30 read as the binary number `0.c(0) c(1) c(2) …₂`. -/
noncomputable def centerBinary : ℝ := ∑' t, (if c t then 1 else 0) / 2 ^ (t + 1)

/-- **Problem 1 as irrationality**: the center column is not eventually periodic iff the binary
number `0.c(0) c(1) c(2) …₂` is irrational. -/
theorem problem1_iff_irrational_binary : Rule30Prize.Problem1 ↔ Irrational centerBinary := by
  have h := problem1_iff_irrational_base (B := 2) le_rfl
  rw [Nat.cast_ofNat] at h
  exact h

/-- The center column of rule 30 read as the decimal number `0.c(0) c(1) c(2) …₁₀`. -/
noncomputable def centerDecimal : ℝ := ∑' t, (if c t then 1 else 0) / 10 ^ (t + 1)

/-- **Problem 1 in decimal**: the center column is not eventually periodic iff the decimal number
`0.c(0) c(1) c(2) …₁₀` (all digits `0` or `1`) is irrational. -/
theorem problem1_iff_irrational_decimal : Rule30Prize.Problem1 ↔ Irrational centerDecimal := by
  have h := problem1_iff_irrational_base (B := 10) (by norm_num)
  rw [Nat.cast_ofNat] at h
  exact h

end Rule30Equivalents.BinaryIrrational
