import Standalone
open Ruliology.CellularAutomata.Rule30Jen
open AbsorbRight

theorem H_0010110_110 : (allLists 10).all (fun rest => traceCol1 (drv [false, false, true, false, true, true, false]) (wbPattern 2 ++ ([true, true, false] ++ rest)) == traceCol1 (drv [false, false, true, false, true, true, false]) (wbPattern 2 ++ List.replicate 13 false)) = true := by decide +kernel
