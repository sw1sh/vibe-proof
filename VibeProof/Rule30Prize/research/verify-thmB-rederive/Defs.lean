import Ruliology.CellularAutomata.Rule30Prize
open Ruliology.CellularAutomata.Rule30Jen Ruliology.CellularAutomata.Rule30Prize
#print Ruliology.CellularAutomata.Rule30Jen.rule
#print Ruliology.CellularAutomata.Rule30Jen.cell
#print Ruliology.CellularAutomata.Rule30Prize.center
#print Ruliology.CellularAutomata.Rule30Jen.EventuallyPeriodic
#eval (List.range 12).map (fun t => if center t then 1 else 0)
