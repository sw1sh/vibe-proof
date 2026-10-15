import Standalone
open AbsorbRight

theorem D4_b010000 : Determined [false, true, false, false, false, false] 4 = true := by decide +kernel
theorem D4_b010010 : Determined [false, true, false, false, true, false] 4 = true := by decide +kernel
theorem D4_b010100 : Determined [false, true, false, true, false, false] 4 = true := by decide +kernel
theorem D4_b010110 : Determined [false, true, false, true, true, false] 4 = true := by decide +kernel
theorem D4_b011000 : Determined [false, true, true, false, false, false] 4 = true := by decide +kernel
theorem D4_b011010 : Determined [false, true, true, false, true, false] 4 = true := by decide +kernel
theorem D4_b011100 : Determined [false, true, true, true, false, false] 4 = true := by decide +kernel
theorem D4_b011110 : Determined [false, true, true, true, true, false] 4 = true := by decide +kernel
