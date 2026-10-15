import Standalone
open AbsorbRight

theorem D4_b000000 : Determined [false, false, false, false, false, false] 4 = true := by decide +kernel
theorem D4_b000010 : Determined [false, false, false, false, true, false] 4 = true := by decide +kernel
theorem D4_b000100 : Determined [false, false, false, true, false, false] 4 = true := by decide +kernel
theorem D4_b000110 : Determined [false, false, false, true, true, false] 4 = true := by decide +kernel
theorem D4_b001000 : Determined [false, false, true, false, false, false] 4 = true := by decide +kernel
theorem D4_b001010 : Determined [false, false, true, false, true, false] 4 = true := by decide +kernel
theorem D4_b001100 : Determined [false, false, true, true, false, false] 4 = true := by decide +kernel
theorem D4_b001110 : Determined [false, false, true, true, true, false] 4 = true := by decide +kernel
