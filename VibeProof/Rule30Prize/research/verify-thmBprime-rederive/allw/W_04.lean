import Standalone
open AbsorbRight

theorem W_w0001 : Determined [false, false, false, true] 4 = true := by decide +kernel
theorem W_w0011 : Determined [false, false, true, true] 4 = true := by decide +kernel
theorem W_w0101 : Determined [false, true, false, true] 4 = true := by decide +kernel
theorem W_w0111 : Determined [false, true, true, true] 4 = true := by decide +kernel
theorem W_w1000 : Determined [true, false, false, false] 4 = true := by decide +kernel
theorem W_w1001 : Determined [true, false, false, true] 4 = true := by decide +kernel
theorem W_w1010 : Determined [true, false, true, false] 4 = true := by decide +kernel
theorem W_w1011 : Determined [true, false, true, true] 4 = true := by decide +kernel
theorem W_w1100 : Determined [true, true, false, false] 4 = true := by decide +kernel
theorem W_w1101 : Determined [true, true, false, true] 4 = true := by decide +kernel
theorem W_w1110 : Determined [true, true, true, false] 4 = true := by decide +kernel
theorem W_w1111 : Determined [true, true, true, true] 4 = true := by decide +kernel
