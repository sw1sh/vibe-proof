import Standalone
open Ruliology.CellularAutomata.Rule30Jen
open AbsorbRight
theorem t1 : Determined [false, true, true, true, false, false, false] 4 = true := by decide +kernel
