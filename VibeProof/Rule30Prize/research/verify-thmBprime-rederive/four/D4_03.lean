import Standalone
open AbsorbRight

theorem D4_b0000 : Determined [false, false, false, false] 4 = true := by decide +kernel
theorem D4_b0010 : Determined [false, false, true, false] 4 = true := by decide +kernel
theorem D4_b0100 : Determined [false, true, false, false] 4 = true := by decide +kernel
theorem D4_b0110 : Determined [false, true, true, false] 4 = true := by decide +kernel
