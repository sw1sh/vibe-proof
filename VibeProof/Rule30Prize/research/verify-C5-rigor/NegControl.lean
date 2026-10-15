import Ruliology.CellularAutomata.Rule30Prize
namespace R30SmallPeriods2
open Ruliology.CellularAutomata.Rule30Jen
def stepW (c : Bool) : List Bool → List Bool
  | [] => []
  | [_] => []
  | x :: y :: rest => rule c x y :: stepW x (y :: rest)
def col1 : List Bool → List Bool → List Bool
  | [], _ => []
  | c :: cs, l => l.headD false :: col1 cs (stepW c l)
def alt (k : Nat) : List Bool := (List.range k).map (fun i => i % 2 == 1)
-- 1100 = C A does occur, so this must FAIL
example : (allLists 6).all (fun l => (col1 (alt 4) l) != [true, true, false, false]) = true := by
  decide +kernel
end R30SmallPeriods2
