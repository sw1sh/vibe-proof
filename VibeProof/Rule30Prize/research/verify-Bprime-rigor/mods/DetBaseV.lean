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


/-- the per-tail test inside `Determined` -/
def G (u : List Bool) (j0 : Nat) (tail : List Bool) : Bool :=
  traceCol1 (drv u) (wbPattern j0 ++ tail) ==
    traceCol1 (drv u) (wbPattern j0 ++ List.replicate (u.length + 10 - 2 * j0) false)

theorem Determined_eq (u : List Bool) (j0 : Nat) :
    Determined u j0 = (allLists (u.length + 10 - 2 * j0)).all (G u j0) := rfl

theorem all_allLists_succ (n : Nat) (g : List Bool → Bool) :
    (allLists (n + 1)).all g =
      ((allLists n).all (fun l => g (false :: l)) && (allLists n).all (fun l => g (true :: l))) := by
  simp only [allLists, List.all_append, List.all_map]
  rfl

end AbsorbRightV
