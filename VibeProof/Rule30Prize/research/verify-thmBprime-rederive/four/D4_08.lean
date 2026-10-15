import Standalone
open AbsorbRight

theorem D4_b0001000 : Determined [false, false, false, true, false, false, false] 4 = true := by decide +kernel
theorem D4_b0001010 : Determined [false, false, false, true, false, true, false] 4 = true := by decide +kernel
theorem D4_b0001100 : Determined [false, false, false, true, true, false, false] 4 = true := by decide +kernel
theorem D4_b0001110 : Determined [false, false, false, true, true, true, false] 4 = true := by decide +kernel
