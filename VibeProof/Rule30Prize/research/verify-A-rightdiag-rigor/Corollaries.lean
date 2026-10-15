import Ruliology.CellularAutomata.Rule30Diagonals

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

namespace Ruliology.CellularAutomata
namespace VerifyCorollaries
open Rule30Jen Rule30Diagonals Rule30DiagonalPeriods

/-- `z` is the length of the maximal white run left of the right edge in row `2^e`. -/
structure IsRun (e z : Nat) : Prop where
  white : ∀ j, 1 ≤ j → j ≤ z → cell (2 ^ e) (((2 ^ e : Nat) : Int) - j) = false
  black : cell (2 ^ e) (((2 ^ e : Nat) : Int) - (z + 1 : Nat)) = true

/-- R_0..R_J all 2^e-periodic iff J ≤ z_e. -/
theorem periodic_iff_le (e z : Nat) (hz : IsRun e z) (J : Nat) :
    (∀ j, j ≤ J → ∀ t, R j (t + 2 ^ e) = R j t) ↔ J ≤ z := by
  rw [R_period_iff]
  constructor
  · intro h
    refine Classical.byContradiction fun hJ => ?_
    have := h (z + 1) (by omega) (by omega)
    rw [hz.black] at this
    exact Bool.noConfusion this
  · intro hJ j h1 h2
    exact hz.white j h1 (by omega)

/-- cell-level copy: cell(t + m 2^e, p + m 2^e) = cell(t, p) for 0 ≤ t - p ≤ z_e. -/
theorem copy_cell (e z : Nat) (hz : IsRun e z) (m t : Nat) (p : Int)
    (h0 : 0 ≤ (t : Int) - p) (h1 : (t : Int) - p ≤ z) :
    cell (t + m * 2 ^ e) (p + ((m * 2 ^ e : Nat) : Int)) = cell t p := by
  have hper := (periodic_iff_le e z hz z).2 (Nat.le_refl z)
  obtain ⟨j, hj⟩ : ∃ j : Nat, (j : Int) = (t : Int) - p := ⟨(t - p).toNat, by omega⟩
  have := right_end_copy e z hper m t j (by omega)
  unfold R at this
  have e1 : (((t + m * 2 ^ e : Nat) : Int) - j) = p + ((m * 2 ^ e : Nat) : Int) := by
    push_cast; omega
  have e2 : ((t : Int) - j) = p := by omega
  rw [e1, e2] at this
  exact this

/-- Row 2^e + s, at its right end, is 0^(z-2s) followed by row s (positions -s..s). -/
theorem row_tail (e z : Nat) (hz : IsRun e z) (s : Nat) (hs : 2 * s ≤ z) (q : Int)
    (hq0 : (s : Int) - z ≤ q) (hq1 : q ≤ s) :
    cell (2 ^ e + s) (((2 ^ e : Nat) : Int) + q) =
      (if q < -(s : Int) then false else cell s q) := by
  have := copy_cell e z hz 1 s q (by omega) (by omega)
  rw [show s + 1 * 2 ^ e = 2 ^ e + s by omega,
    show q + ((1 * 2 ^ e : Nat) : Int) = ((2 ^ e : Nat) : Int) + q by push_cast; omega] at this
  rw [this]
  split
  · exact cell_eq_false_of_lt s q (by omega)
  · rfl

/-- Column 2^e reproduces c(0..z) at times 2^e..2^e+z. -/
theorem column_copy (e z : Nat) (hz : IsRun e z) (t : Nat) (ht : t ≤ z) :
    cell (2 ^ e + t) ((2 ^ e : Nat) : Int) = cell t 0 := by
  have := copy_cell e z hz 1 t 0 (by omega) (by omega)
  rw [show t + 1 * 2 ^ e = 2 ^ e + t by omega,
    show (0 : Int) + ((1 * 2 ^ e : Nat) : Int) = ((2 ^ e : Nat) : Int) by push_cast; omega] at this
  exact this

/-- Bonus (not claimed): R_{z+1} is anti-periodic with anti-period 2^e. -/
theorem next_antiperiodic (e z : Nat) (hz : IsRun e z) (t : Nat) :
    R (z + 1) (t + 2 ^ e) = !R (z + 1) t := by
  have hper := (periodic_iff_le e z hz z).2 (Nat.le_refl z)
  have hb : R (z + 1) (2 ^ e) = true := hz.black
  cases z with
  | zero =>
    have := xor_accum_shift (x := R 1) (g := fun _ => true) (L := 2 ^ e)
      (fun t => R_one_step t) (fun _ => rfl) t
    rw [this, hb, R_start (by omega)]; cases R 1 t <;> rfl
  | succ k =>
    have hg : ∀ t, (R (k + 1) (t + 2 ^ e) || R k (t + 2 ^ e)) = (R (k + 1) t || R k t) := by
      intro t; rw [hper (k + 1) (by omega) t, hper k (by omega) t]
    have := xor_accum_shift (x := R (k + 2)) (g := fun t => R (k + 1) t || R k t)
      (L := 2 ^ e) (fun t => R_step k t) hg t
    rw [this, hb, R_start (by omega)]; cases R (k + 2) t <;> rfl

end VerifyCorollaries
end Ruliology.CellularAutomata

#print axioms Ruliology.CellularAutomata.VerifyCorollaries.periodic_iff_le
#print axioms Ruliology.CellularAutomata.VerifyCorollaries.copy_cell
#print axioms Ruliology.CellularAutomata.VerifyCorollaries.row_tail
#print axioms Ruliology.CellularAutomata.VerifyCorollaries.column_copy
#print axioms Ruliology.CellularAutomata.VerifyCorollaries.next_antiperiodic
