import Ruliology.CellularAutomata.Rule30Prize
-- Definitions copied verbatim from absorb-right/lean/AbsorbRight.lean
namespace DetExtra
open Ruliology.CellularAutomata.Rule30Jen
def stepRow (l : Bool) : List Bool → List Bool
  | a :: b :: rest => rule l a b :: stepRow a (b :: rest)
  | _ => []
def traceCol1 : List Bool → List Bool → List Bool
  | [], row => [row.headD false]
  | c :: cs, row => row.headD false :: traceCol1 cs (stepRow c row)
def wbPattern : Nat → List Bool
  | 0 => []
  | j + 1 => false :: true :: wbPattern j
def drv (u : List Bool) : List Bool := u ++ List.replicate 9 true
def Determined (u : List Bool) (j0 : Nat) : Bool :=
  (allLists (u.length + 10 - 2 * j0)).all fun tail =>
    traceCol1 (drv u) (wbPattern j0 ++ tail) ==
      traceCol1 (drv u) (wbPattern j0 ++ List.replicate (u.length + 10 - 2 * j0) false)
-- the three j0 = 4 blocks (they set the bound r >= 36)
theorem det_011000 : Determined [false, true, true, false, false, false] 4 = true := by decide +kernel
theorem det_0001000 : Determined [false, false, false, true, false, false, false] 4 = true := by decide +kernel
theorem det_0111000 : Determined [false, true, true, true, false, false, false] 4 = true := by decide +kernel
-- minimality of those: j0 = 3 fails
theorem ndet_011000 : Determined [false, true, true, false, false, false] 3 = false := by decide +kernel
-- a length-7 block with j0 = 3 (2048 tails)
theorem det_0000000 : Determined [false, false, false, false, false, false, false] 3 = true := by decide +kernel
end DetExtra
