import Standalone
open AbsorbRight

theorem D4_b0101000 : Determined [false, true, false, true, false, false, false] 4 = true := by decide +kernel
theorem D4_b0101010 : Determined [false, true, false, true, false, true, false] 4 = true := by decide +kernel
theorem D4_b0101100 : Determined [false, true, false, true, true, false, false] 4 = true := by decide +kernel
theorem D4_b0101110 : Determined [false, true, false, true, true, true, false] 4 = true := by decide +kernel
