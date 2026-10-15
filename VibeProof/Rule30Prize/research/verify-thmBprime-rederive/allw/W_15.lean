import Standalone
open AbsorbRight

theorem W_w0011001 : Determined [false, false, true, true, false, false, true] 4 = true := by decide +kernel
theorem W_w0011011 : Determined [false, false, true, true, false, true, true] 4 = true := by decide +kernel
theorem W_w0011101 : Determined [false, false, true, true, true, false, true] 4 = true := by decide +kernel
theorem W_w0011111 : Determined [false, false, true, true, true, true, true] 4 = true := by decide +kernel
