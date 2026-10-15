import Standalone
open AbsorbRight

theorem D4_b0110000 : Determined [false, true, true, false, false, false, false] 4 = true := by decide +kernel
theorem D4_b0110010 : Determined [false, true, true, false, false, true, false] 4 = true := by decide +kernel
theorem D4_b0110100 : Determined [false, true, true, false, true, false, false] 4 = true := by decide +kernel
theorem D4_b0110110 : Determined [false, true, true, false, true, true, false] 4 = true := by decide +kernel
