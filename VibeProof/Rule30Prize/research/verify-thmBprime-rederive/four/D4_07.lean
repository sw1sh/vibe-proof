import Standalone
open AbsorbRight

theorem D4_b0000000 : Determined [false, false, false, false, false, false, false] 4 = true := by decide +kernel
theorem D4_b0000010 : Determined [false, false, false, false, false, true, false] 4 = true := by decide +kernel
theorem D4_b0000100 : Determined [false, false, false, false, true, false, false] 4 = true := by decide +kernel
theorem D4_b0000110 : Determined [false, false, false, false, true, true, false] 4 = true := by decide +kernel
