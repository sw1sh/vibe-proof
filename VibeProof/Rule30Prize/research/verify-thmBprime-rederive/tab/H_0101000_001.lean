import Standalone
open Ruliology.CellularAutomata.Rule30Jen
open AbsorbRight

theorem H_0101000_001 : (allLists 10).all (fun rest => traceCol1 (drv [false, true, false, true, false, false, false]) (wbPattern 2 ++ ([false, false, true] ++ rest)) == traceCol1 (drv [false, true, false, true, false, false, false]) (wbPattern 2 ++ List.replicate 13 false)) = true := by decide +kernel
