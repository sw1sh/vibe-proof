import Standalone
open AbsorbRight

theorem D4_b0111000 : Determined [false, true, true, true, false, false, false] 4 = true := by decide +kernel
theorem D4_b0111010 : Determined [false, true, true, true, false, true, false] 4 = true := by decide +kernel
theorem D4_b0111100 : Determined [false, true, true, true, true, false, false] 4 = true := by decide +kernel
theorem D4_b0111110 : Determined [false, true, true, true, true, true, false] 4 = true := by decide +kernel
