import Standalone
open AbsorbRight

theorem D4_b00000 : Determined [false, false, false, false, false] 4 = true := by decide +kernel
theorem D4_b00010 : Determined [false, false, false, true, false] 4 = true := by decide +kernel
theorem D4_b00100 : Determined [false, false, true, false, false] 4 = true := by decide +kernel
theorem D4_b00110 : Determined [false, false, true, true, false] 4 = true := by decide +kernel
theorem D4_b01000 : Determined [false, true, false, false, false] 4 = true := by decide +kernel
theorem D4_b01010 : Determined [false, true, false, true, false] 4 = true := by decide +kernel
theorem D4_b01100 : Determined [false, true, true, false, false] 4 = true := by decide +kernel
theorem D4_b01110 : Determined [false, true, true, true, false] 4 = true := by decide +kernel
