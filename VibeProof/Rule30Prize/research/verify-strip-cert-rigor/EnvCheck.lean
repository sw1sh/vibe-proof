import Ruliology.CellularAutomata.Rule30Jen
import Ruliology.CellularAutomata.Rule30Prize
open Ruliology.CellularAutomata.Rule30Jen
#print rule
#print cell
#check @not_adjacent
#check @cell_left
#print EventuallyPeriodic
#print axioms not_adjacent
#print axioms cell_left
#print Ruliology.CellularAutomata.Rule30Prize.Problem1
#print Ruliology.CellularAutomata.Rule30Prize.center
-- sanity: first 20 center values
#eval (List.range 12).map (fun t => if cell t 0 then 1 else 0)
