import Ruliology.CellularAutomata.Rule30Prize
namespace AbsorbRightV
open Ruliology.CellularAutomata.Rule30Jen

-- verbatim copies of the definitions from AbsorbRight.lean
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

theorem det_011000 : Determined [false, true, true, false, false, false] 4 = true := by decide +kernel  -- tails 2^8
theorem det_00000 : Determined [false, false, false, false, false] 3 = true := by decide +kernel  -- tails 2^9
theorem det_00010 : Determined [false, false, false, true, false] 3 = true := by decide +kernel  -- tails 2^9
theorem det_00100 : Determined [false, false, true, false, false] 3 = true := by decide +kernel  -- tails 2^9
theorem det_00110 : Determined [false, false, true, true, false] 3 = true := by decide +kernel  -- tails 2^9
theorem det_01000 : Determined [false, true, false, false, false] 3 = true := by decide +kernel  -- tails 2^9
theorem det_0001000 : Determined [false, false, false, true, false, false, false] 4 = true := by decide +kernel  -- tails 2^9
theorem det_0111000 : Determined [false, true, true, true, false, false, false] 4 = true := by decide +kernel  -- tails 2^9
theorem det_000000 : Determined [false, false, false, false, false, false] 3 = true := by decide +kernel  -- tails 2^10
theorem det_000010 : Determined [false, false, false, false, true, false] 3 = true := by decide +kernel  -- tails 2^10
theorem det_000100 : Determined [false, false, false, true, false, false] 3 = true := by decide +kernel  -- tails 2^10
theorem det_000110 : Determined [false, false, false, true, true, false] 3 = true := by decide +kernel  -- tails 2^10
#print axioms det_011000
#print axioms det_00000
#print axioms det_00010
#print axioms det_00100
#print axioms det_00110
#print axioms det_01000
#print axioms det_0001000
#print axioms det_0111000
#print axioms det_000000
#print axioms det_000010
#print axioms det_000100
#print axioms det_000110
end AbsorbRightV
