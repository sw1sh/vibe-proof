import Standalone
open AbsorbRight

theorem W_w1111100 : Determined [true, true, true, true, true, false, false] 4 = true := by decide +kernel
theorem W_w1111101 : Determined [true, true, true, true, true, false, true] 4 = true := by decide +kernel
theorem W_w1111110 : Determined [true, true, true, true, true, true, false] 4 = true := by decide +kernel
theorem W_w1111111 : Determined [true, true, true, true, true, true, true] 4 = true := by decide +kernel
