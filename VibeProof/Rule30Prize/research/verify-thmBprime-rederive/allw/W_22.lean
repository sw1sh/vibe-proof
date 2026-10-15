import Standalone
open AbsorbRight

theorem W_w1001000 : Determined [true, false, false, true, false, false, false] 4 = true := by decide +kernel
theorem W_w1001001 : Determined [true, false, false, true, false, false, true] 4 = true := by decide +kernel
theorem W_w1001010 : Determined [true, false, false, true, false, true, false] 4 = true := by decide +kernel
theorem W_w1001011 : Determined [true, false, false, true, false, true, true] 4 = true := by decide +kernel
