import Ruliology.CellularAutomata.Rule30Prize
open Ruliology.CellularAutomata
#print Rule30Jen.rule
#print Rule30Jen.cell
#print Rule30Jen.EventuallyPeriodic
#print Rule30Prize.center
#print axioms Rule30Jen.not_adjacent
#print axioms Rule30Jen.mem_allLists
example : (List.range 20).map Rule30Prize.center = [true,true,false,true,true,true,false,false,true,true,false,false,false,true,false,true,true,false,false,true] := by decide
