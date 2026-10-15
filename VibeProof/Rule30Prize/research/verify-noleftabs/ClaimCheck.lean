import Ruliology.CellularAutomata.Rule30Jen

/-! Independent restatement of claim A_no_left_absorption, for ANY function `L'` satisfying the
claim's three defining equations (not just one particular recursive definition), proved by
transfer to the scratch file's `L`. Inlined copy of the needed part of DrivenLeft.lean below. -/

namespace VerifyNoLeftAbs
open Ruliology.CellularAutomata.Rule30Jen

def L (c : Nat → Bool) (s : Int → Bool) : Nat → Int → Bool
  | 0, p => if p < 0 then s p else c 0
  | t + 1, p => if p < 0 then rule (L c s t (p - 1)) (L c s t p) (L c s t (p + 1)) else c (t + 1)

/-- Any `L'` obeying the claim's equations agrees with `L` on `p ≤ 0`. -/
theorem agree (c : Nat → Bool) (s : Int → Bool) (L' : Nat → Int → Bool)
    (h0 : ∀ p : Int, p ≤ -1 → L' 0 p = s p)
    (hb : ∀ t, L' t 0 = c t)
    (hr : ∀ t (p : Int), p ≤ -1 → L' (t+1) p = xor (L' t (p-1)) (L' t p || L' t (p+1))) :
    ∀ t (p : Int), p ≤ 0 → L' t p = L c s t p := by
  intro t
  induction t with
  | zero =>
    intro p hp
    by_cases h : p < 0
    · rw [h0 p (by omega)]; simp [L, h]
    · rw [show p = 0 by omega, hb]; simp [L]
  | succ t ih =>
    intro p hp
    by_cases h : p < 0
    · rw [hr t p (by omega), ih (p-1) (by omega), ih p (by omega), ih (p+1) (by omega)]
      simp [L, h, rule]
    · rw [show p = 0 by omega, hb]; simp [L]

end VerifyNoLeftAbs
