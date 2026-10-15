import Ruliology.CellularAutomata.Rule30Prize
open Ruliology.CellularAutomata.Rule30Jen
example (a b c : Bool) : rule a b c = xor a (b || c) := rfl
example (p : Int) : cell 0 p = decide (p = 0) := rfl
example (t : Nat) (p : Int) : cell (t + 1) p = rule (cell t (p - 1)) (cell t p) (cell t (p + 1)) := rfl
#eval (List.range 12).map (fun t => if cell t 0 then 1 else 0)
