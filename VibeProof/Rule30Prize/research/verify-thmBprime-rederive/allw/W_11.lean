import Standalone
open AbsorbRight

theorem W_w111000 : Determined [true, true, true, false, false, false] 4 = true := by decide +kernel
theorem W_w111001 : Determined [true, true, true, false, false, true] 4 = true := by decide +kernel
theorem W_w111010 : Determined [true, true, true, false, true, false] 4 = true := by decide +kernel
theorem W_w111011 : Determined [true, true, true, false, true, true] 4 = true := by decide +kernel
theorem W_w111100 : Determined [true, true, true, true, false, false] 4 = true := by decide +kernel
theorem W_w111101 : Determined [true, true, true, true, false, true] 4 = true := by decide +kernel
theorem W_w111110 : Determined [true, true, true, true, true, false] 4 = true := by decide +kernel
theorem W_w111111 : Determined [true, true, true, true, true, true] 4 = true := by decide +kernel
