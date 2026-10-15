import Ruliology.CellularAutomata.Rule30Prize
open Ruliology.CellularAutomata.Rule30Jen
#print Ruliology.CellularAutomata.Rule30Jen.rule
#print Ruliology.CellularAutomata.Rule30Jen.cell
-- sanity: first center values 1,1,0,1,1,1,0,0,1,1,0,0,0,1
#eval (List.range 12).map (fun t => if cell t 0 then 1 else 0)
