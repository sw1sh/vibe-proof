import Standalone
open AbsorbRight

theorem W_w1110000 : Determined [true, true, true, false, false, false, false] 4 = true := by decide +kernel
theorem W_w1110001 : Determined [true, true, true, false, false, false, true] 4 = true := by decide +kernel
theorem W_w1110010 : Determined [true, true, true, false, false, true, false] 4 = true := by decide +kernel
theorem W_w1110011 : Determined [true, true, true, false, false, true, true] 4 = true := by decide +kernel
