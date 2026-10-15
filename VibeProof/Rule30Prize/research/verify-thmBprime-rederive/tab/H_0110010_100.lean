import Standalone
open Ruliology.CellularAutomata.Rule30Jen
open AbsorbRight

theorem H_0110010_100 : (allLists 10).all (fun rest => traceCol1 (drv [false, true, true, false, false, true, false]) (wbPattern 2 ++ ([true, false, false] ++ rest)) == traceCol1 (drv [false, true, true, false, false, true, false]) (wbPattern 2 ++ List.replicate 13 false)) = true := by decide +kernel
