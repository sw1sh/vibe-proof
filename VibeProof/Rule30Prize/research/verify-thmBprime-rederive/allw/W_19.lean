import Standalone
open AbsorbRight

theorem W_w0111001 : Determined [false, true, true, true, false, false, true] 4 = true := by decide +kernel
theorem W_w0111011 : Determined [false, true, true, true, false, true, true] 4 = true := by decide +kernel
theorem W_w0111101 : Determined [false, true, true, true, true, false, true] 4 = true := by decide +kernel
theorem W_w0111111 : Determined [false, true, true, true, true, true, true] 4 = true := by decide +kernel
