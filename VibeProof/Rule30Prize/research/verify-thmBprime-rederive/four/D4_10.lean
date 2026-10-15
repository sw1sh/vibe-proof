import Standalone
open AbsorbRight

theorem D4_b0011000 : Determined [false, false, true, true, false, false, false] 4 = true := by decide +kernel
theorem D4_b0011010 : Determined [false, false, true, true, false, true, false] 4 = true := by decide +kernel
theorem D4_b0011100 : Determined [false, false, true, true, true, false, false] 4 = true := by decide +kernel
theorem D4_b0011110 : Determined [false, false, true, true, true, true, false] 4 = true := by decide +kernel
