import Standalone
open AbsorbRight

theorem D4_b000 : Determined [false, false, false] 4 = true := by decide +kernel
theorem D4_b010 : Determined [false, true, false] 4 = true := by decide +kernel
