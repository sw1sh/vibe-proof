import Ruliology.CellularAutomata.Rule30Jen
open Ruliology.CellularAutomata.Rule30Jen
-- sanity: first center values 1,1,0,1,1,1,0,0
example : (List.range 8).map (fun t => cell t 0) =
  [true,true,false,true,true,true,false,false] := by decide
-- the defining equations hold definitionally
example (p : Int) : cell 0 p = decide (p = 0) := rfl
example (t : Nat) (p : Int) : cell (t+1) p = rule (cell t (p-1)) (cell t p) (cell t (p+1)) := rfl
