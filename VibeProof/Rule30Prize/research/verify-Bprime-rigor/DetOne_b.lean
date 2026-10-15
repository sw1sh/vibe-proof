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

theorem det_t2 : Determined [false, false, false, false, false] 3 = true := by decide +kernel
end AbsorbRightV
