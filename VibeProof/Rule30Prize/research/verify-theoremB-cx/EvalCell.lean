import Ruliology.CellularAutomata.Rule30Prize
open Ruliology.CellularAutomata.Rule30Jen in
#eval (List.range 13).map (fun t => if cell t 0 then 1 else 0)
open Ruliology.CellularAutomata.Rule30Jen in
#eval (List.range 9).map (fun t => ((List.range 17).map (fun i => if cell t ((i : Int) - 8) then '#' else '.')).asString)
