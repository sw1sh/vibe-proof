import Ruliology.CellularAutomata.Rule30Jen

/-!
# The driven left half never has a periodic column `-1` (scratch)

Run rule 30 on the left half-line `p ≤ -1`, fed at position `0` by an arbitrary column `c`
(`lh x c`). If the initial left half `x` is left-finite and not all white, then column `-1` and
the driver `c` are never both eventually periodic: Jen's argument (left-permutivity plus the
left edge) runs inside the half-line.

So, unlike the right half, the left half has no "absorbing words": for an eventually periodic
driver, column `-1` is always aperiodic. (The non-adjacent case, any column `-m`, follows from the
strip argument exactly as in `Rule30Jen.between_periodic`; not repeated here.)
-/

namespace R30LeftDriven
open Ruliology.CellularAutomata.Rule30Jen

/-- The left half driven by `c`; position `0` holds `c t` (positions `≥ 1` are unused). -/
def lh (x : Int → Bool) (c : Nat → Bool) : Nat → Int → Bool
  | 0, p => if p = 0 then c 0 else x p
  | t + 1, p => if p = 0 then c (t + 1) else rule (lh x c t (p - 1)) (lh x c t p) (lh x c t (p + 1))

theorem lh_zero (x : Int → Bool) (c : Nat → Bool) : ∀ t, lh x c t 0 = c t
  | 0 => rfl
  | _ + 1 => rfl

theorem lh_step (x : Int → Bool) (c : Nat → Bool) (t : Nat) {p : Int} (hp : p ≤ -1) :
    lh x c (t + 1) p = rule (lh x c t (p - 1)) (lh x c t p) (lh x c t (p + 1)) := by
  show (if p = 0 then c (t + 1) else _) = _
  rw [if_neg (by omega)]

section edge
variable (x : Int → Bool) (c : Nat → Bool) (q : Int) (hq : q ≤ -1) (hx : x q = true)
  (hw : ∀ p, p < q → x p = false)
include hq hw

theorem lh_white : ∀ (t : Nat) (p : Int), p < q - t → lh x c t p = false
  | 0, p, h => by
    show (if p = 0 then c 0 else x p) = false
    rw [if_neg (by omega)]; exact hw p (by omega)
  | t + 1, p, h => by
    rw [lh_step x c t (by omega), lh_white t (p - 1) (by omega), lh_white t p (by omega),
      lh_white t (p + 1) (by omega)]
    rfl

include hx in
theorem lh_edge : ∀ t : Nat, lh x c t (q - t) = true
  | 0 => by
    show (if q - ((0 : Nat) : Int) = 0 then c 0 else x (q - ((0 : Nat) : Int))) = true
    rw [if_neg (by omega), show q - ((0 : Nat) : Int) = q by omega]; exact hx
  | t + 1 => by
    rw [lh_step x c t (by omega), lh_white x c q hq hw t _ (by omega),
      lh_white x c q hq hw t _ (by omega), show q - ((t + 1 : Nat) : Int) + 1 = q - t by omega,
      lh_edge t]
    rfl
end edge

/-- Left-permutivity inside the half-line (needs `i ≤ -1`, so it uses columns `i`, `i + 1 ≤ 0`). -/
theorem lh_left (x : Int → Bool) (c : Nat → Bool) (t : Nat) {i : Int} (hi : i ≤ -1) :
    lh x c t (i - 1) = xor (lh x c (t + 1) i) (lh x c t i || lh x c t (i + 1)) := by
  rw [lh_step x c t hi]
  cases lh x c t (i - 1) <;> cases lh x c t i <;> cases lh x c t (i + 1) <;> rfl

theorem periodic_left_all (x : Int → Bool) (c : Nat → Bool) {T P : Nat}
    (h0 : ∀ t, T ≤ t → lh x c (t + P) (-1) = lh x c t (-1))
    (h1 : ∀ t, T ≤ t → lh x c (t + P) 0 = lh x c t 0) :
    ∀ m : Nat, (∀ t, T ≤ t → lh x c (t + P) (-1 - m) = lh x c t (-1 - m)) ∧
      ∀ t, T ≤ t → lh x c (t + P) (-1 - m + 1) = lh x c t (-1 - m + 1) := by
  intro m
  induction m with
  | zero => simpa using ⟨h0, h1⟩
  | succ m ih =>
    refine ⟨fun t ht => ?_, ?_⟩
    · have hi : (-1 - (m : Int)) ≤ -1 := by omega
      rw [show (-1 : Int) - ((m + 1 : Nat) : Int) = (-1 - (m : Int)) - 1 by omega,
        lh_left x c (t + P) hi, lh_left x c t hi, show t + P + 1 = (t + 1) + P by omega,
        ih.1 (t + 1) (by omega), ih.1 t ht, ih.2 t ht]
    · rw [show (-1 : Int) - ((m + 1 : Nat) : Int) + 1 = -1 - (m : Int) by omega]
      exact ih.1

/-- **Jen's theorem in the driven left half**: for a left-finite, not all white, initial left half,
column `-1` and the driver are never both eventually periodic. -/
theorem not_both_periodic (x : Int → Bool) (c : Nat → Bool) (q : Int) (hq : q ≤ -1)
    (hx : x q = true) (hw : ∀ p, p < q → x p = false)
    (hc : EventuallyPeriodic c) (h1 : EventuallyPeriodic fun t => lh x c t (-1)) : False := by
  obtain ⟨T, P, hP, hp1, hpc⟩ := common_period h1 hc
  have hp0 : ∀ t, T ≤ t → lh x c (t + P) 0 = lh x c t 0 := fun t ht => by
    rw [lh_zero, lh_zero]; exact hpc t ht
  -- a column far to the left, reached by the edge after time T + P
  obtain ⟨m, hm⟩ : ∃ m : Nat, (-1 - (m : Int)) = q - ((T + P : Nat) : Int) - 1 :=
    ⟨(-q + T + P).toNat, by omega⟩
  have hper := (periodic_left_all x c hp1 hp0 m).1 (T + 1) (Nat.le_succ T)
  rw [hm] at hper
  have hedge := lh_edge x c q hq hx hw (T + P + 1)
  rw [show q - ((T + P + 1 : Nat) : Int) = q - ((T + P : Nat) : Int) - 1 by omega,
    show T + P + 1 = T + 1 + P by omega] at hedge
  have hwhite := lh_white x c q hq hw (T + 1) (q - ((T + P : Nat) : Int) - 1) (by omega)
  rw [hedge, hwhite] at hper
  exact absurd hper (by decide)

end R30LeftDriven
