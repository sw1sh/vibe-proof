import Ruliology.CellularAutomata.Rule30Prize
open Ruliology.CellularAutomata
#print axioms Rule30Jen.not_adjacent
#print axioms Rule30Jen.cell_left
#check @Rule30Prize.no_column_eventually_constant
#print axioms Rule30Prize.no_column_eventually_constant
-- sanity: first 14 centre values from the Lean definition
#eval (List.range 14).map (fun t => if Rule30Jen.cell t 0 then 1 else 0)
