import Ruliology.CellularAutomata.Rule30Prize

/-!
Independent re-check of claim C1 (effective boundary) including the "Hence" statement
(the actual left half equals the half-line evolution driven by c'(t) = c(t) && c(t+1))
and corollary (ii) (ZBL under a period word with no cyclically adjacent 1s).
-/

namespace VerifyC1
open Ruliology.CellularAutomata.Rule30Jen
open Ruliology.CellularAutomata.Rule30Prize

theorem cell_succ (t : Nat) (p : Int) :
    cell (t + 1) p = rule (cell t (p - 1)) (cell t p) (cell t (p + 1)) := rfl

/-- The identity. -/
theorem effective_boundary (t : Nat) :
    (cell t (-1) || center t) = (cell t (-1) || (center t && center (t + 1))) := by
  have hl := cell_left t 0
  rw [show (0 : Int) - 1 = -1 by rfl] at hl
  unfold center
  rw [hl]
  cases cell (t + 1) 0 <;> cases cell t 0 <;> cases cell t (0 + 1) <;> rfl

/-- Corollary (i). -/
theorem left_of_black (t : Nat) (h : center t = true) :
    cell t (-1) = !center (t + 1) := by
  have hl := cell_left t 0
  rw [show (0 : Int) - 1 = -1 by rfl] at hl
  unfold center at h ⊢
  rw [hl, h]
  cases cell (t + 1) 0 <;> rfl

/-- One step of rule 30 on the half-line `p ≤ -1`, with `d` standing in for column 0.
Cells at `p ≥ 0` are set to `false`; they are never read. -/
def drivenStep (d : Bool) (s : Int → Bool) : Int → Bool := fun p =>
  if p ≤ -2 then rule (s (p - 1)) (s p) (s (p + 1))
  else if p = -1 then rule (s (-2)) (s (-1)) d
  else false

/-- Half-line evolution driven by `d`, started at time `T` from `s0`;
`driven d s0 T k` is the state at time `T + k`. -/
def driven (d : Nat → Bool) (s0 : Int → Bool) (T : Nat) : Nat → Int → Bool
  | 0 => s0
  | k + 1 => drivenStep (d (T + k)) (driven d s0 T k)

/-- The effective driver c'(t) = c(t) && c(t+1). -/
def cEff (t : Nat) : Bool := center t && center (t + 1)

/-- **Hence**: from any start time `T`, the actual left half is the half-line evolution driven
by `cEff`, started from the actual left half at time `T`. -/
theorem left_half_driven (T : Nat) : ∀ (k : Nat) (p : Int), p ≤ -1 →
    driven cEff (cell T) T k p = cell (T + k) p
  | 0, p, _ => rfl
  | k + 1, p, hp => by
    have ih := left_half_driven T k
    show drivenStep (cEff (T + k)) (driven cEff (cell T) T k) p = cell (T + k + 1) p
    unfold drivenStep
    by_cases h2 : p ≤ -2
    · rw [if_pos h2, ih (p - 1) (by omega), ih p (by omega), ih (p + 1) (by omega)]
      rfl
    · rw [if_neg h2]
      have h1 : p = -1 := by omega
      subst h1
      rw [if_pos rfl, ih (-2) (by omega), ih (-1) (by omega)]
      have hb := effective_boundary (T + k)
      show xor (cell (T + k) (-2)) (cell (T + k) (-1) || (center (T + k) && center (T + k + 1))) =
        xor (cell (T + k) (-1 - 1)) (cell (T + k) (-1) || cell (T + k) (-1 + 1))
      rw [← hb]
      rfl

/-- The same with the ORIGINAL driver c (sanity: the brief's driven-halves framework). -/
theorem left_half_driven_c (T : Nat) : ∀ (k : Nat) (p : Int), p ≤ -1 →
    driven center (cell T) T k p = cell (T + k) p
  | 0, p, _ => rfl
  | k + 1, p, hp => by
    have ih := left_half_driven_c T k
    show drivenStep (center (T + k)) (driven center (cell T) T k) p = cell (T + k + 1) p
    unfold drivenStep
    by_cases h2 : p ≤ -2
    · rw [if_pos h2, ih (p - 1) (by omega), ih p (by omega), ih (p + 1) (by omega)]
      rfl
    · rw [if_neg h2]
      have h1 : p = -1 := by omega
      subst h1
      rw [if_pos rfl, ih (-2) (by omega), ih (-1) (by omega)]
      rfl

theorem driven_congr (d d' : Nat → Bool) (s0 : Int → Bool) (T : Nat)
    (h : ∀ k, d (T + k) = d' (T + k)) : ∀ k, driven d s0 T k = driven d' s0 T k
  | 0 => rfl
  | k + 1 => by
    show drivenStep (d (T + k)) (driven d s0 T k) = drivenStep (d' (T + k)) (driven d' s0 T k)
    rw [h k, driven_congr d d' s0 T h k]

/-- The autonomous zero-boundary left half (ZBL). -/
def zbl (s0 : Int → Bool) (T : Nat) : Nat → Int → Bool := driven (fun _ => false) s0 T

/-- **Corollary (ii)**, with the period word `w` given as a function on `0..P-1` and the
center column equal to `w ((t - T) % P)` for `t ≥ T`. -/
theorem corollary_ii (T P : Nat) (hP : 0 < P) (w : Nat → Bool)
    (hc : ∀ t, T ≤ t → center t = w ((t - T) % P))
    (hw : ∀ i, i < P → (w i && w ((i + 1) % P)) = false) :
    (∀ (k : Nat) (p : Int), p ≤ -1 → zbl (cell T) T k p = cell (T + k) p) ∧
    (∀ t, T ≤ t → center t = true → cell t (-1) = true) := by
  have hnoadj : ∀ t, T ≤ t → cEff t = false := by
    intro t ht
    unfold cEff
    rw [hc t ht, hc (t + 1) (by omega), show t + 1 - T = (t - T) + 1 by omega,
      ← Nat.mod_add_mod (t - T) P 1]
    exact hw _ (Nat.mod_lt _ hP)
  constructor
  · intro k p hp
    unfold zbl
    rw [← driven_congr cEff (fun _ => false) (cell T) T (fun k => hnoadj (T + k) (by omega)) k]
    exact left_half_driven T k p hp
  · intro t ht hct
    rw [left_of_black t hct]
    have h := hnoadj t ht
    unfold cEff at h
    rw [hct] at h
    simp only [Bool.true_and] at h
    rw [h]
    rfl

/-- Variant of (ii) phrased directly with eventual periodicity and the word `c(T..T+P-1)`. -/
theorem corollary_ii' (T P : Nat) (hP : 0 < P)
    (hper : ∀ t, T ≤ t → center (t + P) = center t)
    (hw : ∀ i, i < P → (center (T + i) && center (T + (i + 1) % P)) = false) :
    (∀ (k : Nat) (p : Int), p ≤ -1 → zbl (cell T) T k p = cell (T + k) p) ∧
    (∀ t, T ≤ t → center t = true → cell t (-1) = true) := by
  have hperk : ∀ q t, T ≤ t → center (t + q * P) = center t := by
    intro q; induction q with
    | zero => intro t _; simp
    | succ q ih => intro t ht; rw [show t + (q + 1) * P = (t + q * P) + P by
        rw [Nat.succ_mul]; omega, hper _ (by omega), ih t ht]
  have hc : ∀ t, T ≤ t → center t = (fun i => center (T + i)) ((t - T) % P) := by
    intro t ht
    have hq : t = (T + (t - T) % P) + ((t - T) / P) * P := by
      have := Nat.mod_add_div (t - T) P; rw [Nat.mul_comm] at this; omega
    show center t = center (T + (t - T) % P)
    conv => lhs; rw [hq]
    rw [hperk _ _ (by omega)]
  exact corollary_ii T P hP (fun i => center (T + i)) hc hw

/-- The starting configuration of (ii) is finite. -/
theorem start_finite (T : Nat) (p : Int) (hp : p < -(T : Int)) : cell T p = false :=
  cell_eq_false_of_lt T p hp

end VerifyC1

#print axioms VerifyC1.effective_boundary
#print axioms VerifyC1.left_of_black
#print axioms VerifyC1.left_half_driven
#print axioms VerifyC1.left_half_driven_c
#print axioms VerifyC1.corollary_ii
#print axioms VerifyC1.corollary_ii'
#print axioms VerifyC1.start_finite
