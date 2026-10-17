import Ruliology.CellularAutomata.Rule30PeriodTwoCoupled
import Ruliology.CellularAutomata.Rule30Realization

/-!
Scratch (r30equiv / ca-structure): `CQ01` is exactly the statement that no finite configuration has
center trace `1, 0, 1, 0, …` (the period-2 case of the finite-configuration version of Problem 1).
-/

namespace R30EquivScratch2
open Ruliology.CellularAutomata
open Rule30Jen Rule30Realization Rule30ZeroBoundary Rule30PeriodTwoCoupled
open Rule30Ether (drv drv_col0 drv_init)

/-- A configuration with finitely many black cells. -/
def FinConfig (x : Int → Bool) : Prop := ∃ W : Nat, ∀ p : Int, W < p.natAbs → x p = false

theorem altCol_even (s : Nat) : altCol (2 * s) = true := by
  unfold altCol; rw [show 2 * s % 2 = 0 by omega]; rfl

theorem altCol_odd (s : Nat) : altCol (2 * s + 1) = false := by
  unfold altCol; rw [show (2 * s + 1) % 2 = 1 by omega]; rfl

theorem evol_congr {x : Int → Bool} {t : Nat} {p q : Int} (h : p = q) : evol x t p = evol x t q :=
  h ▸ rfl

/-! ### From a finite configuration with alternating center to a violation of `CQ01` -/

section Forward
variable (x : Int → Bool) (hx : ∀ t, evol x t 0 = altCol t)
include hx

theorem center_step (t : Nat) :
    altCol (t + 1) = xor (evol x t (-1)) (altCol t || evol x t 1) := by
  rw [← hx (t + 1), ← hx t]
  show rule (evol x t (0 - 1)) (evol x t 0) (evol x t (0 + 1)) = _
  rfl

theorem col_m1_even (s : Nat) : evol x (2 * s) (-1) = true := by
  have h := center_step x hx (2 * s)
  rw [altCol_even, show 2 * s + 1 = 2 * s + 1 from rfl, altCol_odd] at h
  revert h; cases evol x (2 * s) (-1) <;> simp

theorem col_m1_odd (s : Nat) : evol x (2 * s + 1) (-1) = !evol x (2 * s + 1) 1 := by
  have h := center_step x hx (2 * s + 1)
  rw [show 2 * s + 1 + 1 = 2 * (s + 1) by omega, altCol_even, altCol_odd] at h
  revert h; cases evol x (2 * s + 1) (-1) <;> cases evol x (2 * s + 1) 1 <;> simp

theorem right_is_drv : ∀ (t p : Nat), drv altCol (fun p => x (p : Int)) t p = evol x t (p : Int)
  | 0, 0 => by rw [drv_col0]; exact (hx 0).symm
  | 0, p + 1 => drv_init _ _ (p + 1) (by omega)
  | t + 1, 0 => by rw [drv_col0]; exact (hx (t + 1)).symm
  | t + 1, p + 1 => by
    show rule (drv altCol _ t p) (drv altCol _ t (p + 1)) (drv altCol _ t (p + 2)) =
      rule (evol x t (((p + 1 : Nat) : Int) - 1)) (evol x t ((p + 1 : Nat) : Int))
        (evol x t (((p + 1 : Nat) : Int) + 1))
    rw [right_is_drv t p, right_is_drv t (p + 1), right_is_drv t (p + 2),
      evol_congr (show ((p + 1 : Nat) : Int) - 1 = (p : Int) by omega),
      evol_congr (show ((p + 1 : Nat) : Int) + 1 = ((p + 2 : Nat) : Int) by omega)]

theorem left_is_zrow :
    ∀ (t k : Nat), 1 ≤ k → zrow (fun k => x (-(k : Int))) t k = evol x t (-(k : Int))
  | 0, k, hk => zrow_zero_of_pos _ hk
  | t + 1, k, hk => by
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [zrow_succ]
    show _ = rule (evol x t (-((j + 1 : Nat) : Int) - 1)) (evol x t (-((j + 1 : Nat) : Int)))
      (evol x t (-((j + 1 : Nat) : Int) + 1))
    rw [left_is_zrow t (j + 2) (by omega), left_is_zrow t (j + 1) (by omega),
      evol_congr (show -((j + 1 : Nat) : Int) - 1 = -((j + 2 : Nat) : Int) by omega)]
    cases j with
    | zero =>
      rw [zrow_wall, evol_congr (show -((0 + 1 : Nat) : Int) + 1 = 0 by omega), hx t]
      obtain ⟨s, rfl | rfl⟩ : ∃ s, t = 2 * s ∨ t = 2 * s + 1 := ⟨t / 2, by omega⟩
      · rw [evol_congr (show -((0 + 1 : Nat) : Int) = -1 by omega), col_m1_even x hx s]; rfl
      · rw [altCol_odd]; rfl
    | succ j =>
      rw [left_is_zrow t (j + 1) (by omega),
        evol_congr (show -((j + 1 + 1 : Nat) : Int) + 1 = -((j + 1 : Nat) : Int) by omega)]
      rfl

end Forward

/-! ### From a violation of `CQ01` to a finite configuration with alternating center -/

/-- Glue a left half `L` (depth `k` at position `-k`), a black center and a right half `R`. -/
def glue (L R : Nat → Bool) (p : Int) : Bool :=
  if p < 0 then L (-p).toNat else if p = 0 then true else R p.toNat

/-- The claimed evolution: the zero-boundary left half and the right half driven by `altCol`. -/
def gluedRun (L R : Nat → Bool) (t : Nat) (p : Int) : Bool :=
  if p < 0 then zrow L t (-p).toNat else drv altCol R t p.toNat

theorem evol_glue (L R : Nat → Bool) (hX : ∀ s, zrow L (2 * s) 1 = true)
    (hC : ∀ s, zrow L (2 * s + 1) 1 = !drv altCol R (2 * s + 1) 1) :
    ∀ t p, evol (glue L R) t p = gluedRun L R t p
  | 0, p => by
    show glue L R p = gluedRun L R 0 p
    unfold glue gluedRun
    by_cases h : p < 0
    · rw [if_pos h, if_pos h]
      obtain ⟨k, hk⟩ : ∃ k : Nat, (-p).toNat = k + 1 := ⟨(-p).toNat - 1, by omega⟩
      rw [hk]; rfl
    · rw [if_neg h, if_neg h]
      by_cases h0 : p = 0
      · rw [if_pos h0, show p.toNat = 0 by omega, drv_col0]; rfl
      · rw [if_neg h0, drv_init _ _ _ (by omega)]
  | t + 1, p => by
    show rule (evol (glue L R) t (p - 1)) (evol (glue L R) t p) (evol (glue L R) t (p + 1)) =
      gluedRun L R (t + 1) p
    rw [evol_glue L R hX hC t (p - 1), evol_glue L R hX hC t p, evol_glue L R hX hC t (p + 1)]
    rcases (show p ≤ -2 ∨ p = -1 ∨ p = 0 ∨ p = 1 ∨ 2 ≤ p by omega) with h | h | h | h | h
    · -- deep in the left half
      unfold gluedRun
      rw [if_pos (show p - 1 < 0 by omega), if_pos (show p < 0 by omega),
        if_pos (show p + 1 < 0 by omega), if_pos (show p < 0 by omega)]
      obtain ⟨k, hk⟩ : ∃ k : Nat, (-p).toNat = k + 2 := ⟨(-p).toNat - 2, by omega⟩
      rw [show (-(p - 1)).toNat = k + 3 by omega, hk, show (-(p + 1)).toNat = k + 1 by omega]
      rfl
    · -- column -1: the wall is white, and the center is black only where column -1 is
      unfold gluedRun
      rw [if_pos (show p - 1 < 0 by omega), if_pos (show p < 0 by omega),
        if_neg (show ¬ p + 1 < 0 by omega), if_pos (show p < 0 by omega),
        show (-(p - 1)).toNat = 2 by omega, show (-p).toNat = 1 by omega,
        show (p + 1).toNat = 0 by omega, drv_col0, zrow_succ L t 0, zrow_wall]
      show xor (zrow L t 2) (zrow L t 1 || altCol t) = xor (zrow L t 2) (zrow L t 1 || false)
      obtain ⟨s, rfl | rfl⟩ : ∃ s, t = 2 * s ∨ t = 2 * s + 1 := ⟨t / 2, by omega⟩
      · rw [hX s]; rfl
      · rw [altCol_odd]
    · -- the center
      unfold gluedRun
      rw [if_pos (show p - 1 < 0 by omega), if_neg (show ¬ p < 0 by omega),
        if_neg (show ¬ p + 1 < 0 by omega), if_neg (show ¬ p < 0 by omega),
        show (-(p - 1)).toNat = 1 by omega, show p.toNat = 0 by omega,
        show (p + 1).toNat = 1 by omega, drv_col0, drv_col0]
      show xor (zrow L t 1) (altCol t || drv altCol R t 1) = altCol (t + 1)
      obtain ⟨s, rfl | rfl⟩ : ∃ s, t = 2 * s ∨ t = 2 * s + 1 := ⟨t / 2, by omega⟩
      · rw [hX s, altCol_even, altCol_odd]; rfl
      · rw [hC s, altCol_odd, show 2 * s + 1 + 1 = 2 * (s + 1) by omega, altCol_even]
        cases drv altCol R (2 * s + 1) 1 <;> rfl
    · -- column 1
      unfold gluedRun
      rw [if_neg (show ¬ p - 1 < 0 by omega), if_neg (show ¬ p < 0 by omega),
        if_neg (show ¬ p + 1 < 0 by omega), if_neg (show ¬ p < 0 by omega),
        show (p - 1).toNat = 0 by omega, show p.toNat = 0 + 1 by omega,
        show (p + 1).toNat = 2 by omega]
      rfl
    · -- deep in the right half
      unfold gluedRun
      rw [if_neg (show ¬ p - 1 < 0 by omega), if_neg (show ¬ p < 0 by omega),
        if_neg (show ¬ p + 1 < 0 by omega), if_neg (show ¬ p < 0 by omega)]
      obtain ⟨k, hk⟩ : ∃ k : Nat, p.toNat = k + 1 := ⟨p.toNat - 1, by omega⟩
      rw [show (p - 1).toNat = k by omega, hk, show (p + 1).toNat = k + 2 by omega]
      rfl

/-- **`CQ01` is the period-2 case of the finite-configuration problem**: it holds exactly when no
configuration with finitely many black cells has center column `1, 0, 1, 0, …` from time `0`. -/
theorem CQ01_iff_no_finite_alternating :
    CQ01 ↔ ¬ ∃ x : Int → Bool, FinConfig x ∧ ∀ t, evol x t 0 = altCol t := by
  constructor
  · rintro hC ⟨x, ⟨W, hW⟩, hx⟩
    apply hC
    refine ⟨fun k => x (-(k : Int)), fun p => x (p : Int), ⟨W, fun k hk => hW _ (by omega)⟩,
      ⟨W, fun p hp => hW _ (by omega)⟩, fun s => ?_, fun s => ?_⟩
    · rw [left_is_zrow x hx (2 * s) 1 (by omega)]
      exact (evol_congr (by omega)).trans (col_m1_even x hx s)
    · rw [left_is_zrow x hx (2 * s + 1) 1 (by omega), right_is_drv x hx (2 * s + 1) 1,
        evol_congr (show -((1 : Nat) : Int) = -1 by omega)]
      exact col_m1_odd x hx s
  · rintro h ⟨L, R, ⟨WL, hL⟩, ⟨WR, hR⟩, hX, hC⟩
    apply h
    refine ⟨glue L R, ⟨max WL WR, fun p hp => ?_⟩, fun t => ?_⟩
    · unfold glue
      by_cases hn : p < 0
      · rw [if_pos hn]; exact hL _ (by omega)
      · rw [if_neg hn, if_neg (by omega)]; exact hR _ (by omega)
    · rw [evol_glue L R hX hC t 0]
      unfold gluedRun
      rw [if_neg (by omega)]
      exact drv_col0 _ _ t

/-- **`Q01` already covers every configuration whose left half is finite** (number-like in Kopra's
sense; the right half is arbitrary): none has center column `1, 0, 1, 0, …` from time `0`. -/
theorem Q01_no_leftfinite_alternating (hQ : Rule30ZeroBoundary.Q01) :
    ¬ ∃ x : Int → Bool, (∃ W : Nat, ∀ p : Int, p < -(W : Int) → x p = false) ∧
      ∀ t, evol x t 0 = altCol t := by
  rintro ⟨x, ⟨W, hW⟩, hx⟩
  refine hQ (fun k => x (-(k : Int))) ⟨W, fun k hk => hW _ (by omega)⟩ (fun s => ?_)
  rw [left_is_zrow x hx (2 * s) 1 (by omega)]
  exact (evol_congr (by omega)).trans (col_m1_even x hx s)

end R30EquivScratch2

#print axioms R30EquivScratch2.CQ01_iff_no_finite_alternating
#print axioms R30EquivScratch2.Q01_no_leftfinite_alternating
