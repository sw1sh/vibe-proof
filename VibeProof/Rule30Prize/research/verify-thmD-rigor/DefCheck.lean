import Ruliology.CellularAutomata.Rule30Prize
open Ruliology.CellularAutomata.Rule30Jen Ruliology.CellularAutomata.Rule30Prize
example (p : Int) : cell 0 p = decide (p = 0) := rfl
example (t : Nat) (p : Int) : cell (t+1) p = rule (cell t (p-1)) (cell t p) (cell t (p+1)) := rfl
example : (List.range 20).map center =
  [true,true,false,true,true,true,false,false,true,true,false,false,false,true,false,true,true,false,false,true] := by decide +kernel
-- rule 30 truth table: 111..000 -> 0,0,0,1,1,1,1,0
example : [rule true true true, rule true true false, rule true false true, rule true false false,
  rule false true true, rule false true false, rule false false true, rule false false false] =
  [false,false,false,true,true,true,true,false] := rfl
