import Standalone
open AbsorbRight

theorem D4_b0010000 : Determined [false, false, true, false, false, false, false] 4 = true := by decide +kernel
theorem D4_b0010010 : Determined [false, false, true, false, false, true, false] 4 = true := by decide +kernel
theorem D4_b0010100 : Determined [false, false, true, false, true, false, false] 4 = true := by decide +kernel
theorem D4_b0010110 : Determined [false, false, true, false, true, true, false] 4 = true := by decide +kernel
