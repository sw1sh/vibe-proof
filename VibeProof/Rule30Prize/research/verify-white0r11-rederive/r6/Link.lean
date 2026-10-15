import Ruliology.CellularAutomata.Rule30Prize
import Std.Tactic.BVDecide

namespace R30W6
open Ruliology.CellularAutomata.Rule30Jen
open Ruliology.CellularAutomata.Rule30Prize

/-- Driver for `w = 00000011` at phase 0. -/
def drv (t : Nat) : Bool := decide (6 ≤ t % 8)

def stepBV {W : Nat} (d : Bool) (r : BitVec W) : BitVec W :=
  ((r <<< 1) ||| (if d then 1#W else 0#W)) ^^^ (r ||| (r >>> 1))

def row0 (a W : Nat) : BitVec W :=
  (BitVec.ofBoolListLE ((List.range W).map (fun i => cell a ((i + 1 : Nat) : Int)))).setWidth W

def model (a W : Nat) : Nat → BitVec W
  | 0 => row0 a W
  | t + 1 => stepBV (drv t) (model a W t)

theorem row0_bit (a W i : Nat) (hi : i < W) : (row0 a W).getLsbD i = cell a ((i + 1 : Nat) : Int) := by
  simp only [row0, BitVec.getLsbD_setWidth, BitVec.getLsbD_ofBoolListLE, List.getD_eq_getElem?_getD,
    List.getElem?_map, List.getElem?_range hi, Option.map_some, Option.getD_some, decide_eq_true hi,
    Bool.true_and]

theorem model_bit (a W : Nat) (hd : ∀ t, cell (a + t) 0 = drv t) :
    ∀ t i, i + t < W → (model a W t).getLsbD i = cell (a + t) ((i + 1 : Nat) : Int)
  | 0, i, h => by simpa using row0_bit a W i (by omega)
  | t + 1, i, h => by
    have ih := model_bit a W hd t
    have hc : cell (a + (t + 1)) ((i + 1 : Nat) : Int) =
        rule (cell (a + t) (((i + 1 : Nat) : Int) - 1)) (cell (a + t) ((i + 1 : Nat) : Int))
          (cell (a + t) (((i + 1 : Nat) : Int) + 1)) := rfl
    rw [hc]
    show (stepBV (drv t) (model a W t)).getLsbD i = _
    simp only [stepBV, BitVec.getLsbD_xor, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft,
      BitVec.getLsbD_ushiftRight]
    have hcen := ih i (by omega)
    have hrt := ih (1 + i) (by omega)
    rw [show ((1 + i + 1 : Nat) : Int) = ((i + 1 : Nat) : Int) + 1 by omega] at hrt
    rw [hcen, hrt]
    rcases Nat.eq_zero_or_pos i with h0 | hpos
    · subst h0
      have hdt := hd t
      rw [show ((0 + 1 : Nat) : Int) - 1 = 0 by rfl, hdt]
      cases hdrv : drv t <;> simp [rule, show 0 < W by omega]
    · have hlt := ih (i - 1) (by omega)
      rw [show ((i - 1 + 1 : Nat) : Int) = ((i + 1 : Nat) : Int) - 1 by omega] at hlt
      rw [hlt]
      have hne : i ≠ 0 := by omega
      cases hdrv : drv t <;> simp [rule, hne, show i < W by omega, show ¬ i < 1 by omega]

end R30W6
