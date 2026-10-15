import Standalone
open AbsorbRight

theorem D4_b0100000 : Determined [false, true, false, false, false, false, false] 4 = true := by decide +kernel
theorem D4_b0100010 : Determined [false, true, false, false, false, true, false] 4 = true := by decide +kernel
theorem D4_b0100100 : Determined [false, true, false, false, true, false, false] 4 = true := by decide +kernel
theorem D4_b0100110 : Determined [false, true, false, false, true, true, false] 4 = true := by decide +kernel
