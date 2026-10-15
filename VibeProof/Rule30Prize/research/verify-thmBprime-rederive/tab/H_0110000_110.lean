import Standalone
open Ruliology.CellularAutomata.Rule30Jen
open AbsorbRight

theorem H_0110000_110 : (allLists 10).all (fun rest => traceCol1 (drv [false, true, true, false, false, false, false]) (wbPattern 2 ++ ([true, true, false] ++ rest)) == traceCol1 (drv [false, true, true, false, false, false, false]) (wbPattern 2 ++ List.replicate 13 false)) = true := by decide +kernel
