import Standalone
open AbsorbRight

theorem W_w1111000 : Determined [true, true, true, true, false, false, false] 4 = true := by decide +kernel
theorem W_w1111001 : Determined [true, true, true, true, false, false, true] 4 = true := by decide +kernel
theorem W_w1111010 : Determined [true, true, true, true, false, true, false] 4 = true := by decide +kernel
theorem W_w1111011 : Determined [true, true, true, true, false, true, true] 4 = true := by decide +kernel
