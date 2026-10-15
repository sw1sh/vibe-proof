import Standalone
open Ruliology.CellularAutomata.Rule30Jen
open AbsorbRight

theorem H_0000100_000 : (allLists 10).all (fun rest => traceCol1 (drv [false, false, false, false, true, false, false]) (wbPattern 2 ++ ([false, false, false] ++ rest)) == traceCol1 (drv [false, false, false, false, true, false, false]) (wbPattern 2 ++ List.replicate 13 false)) = true := by decide +kernel
