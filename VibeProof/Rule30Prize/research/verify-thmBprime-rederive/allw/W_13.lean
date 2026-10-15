import Standalone
open AbsorbRight

theorem W_w0001001 : Determined [false, false, false, true, false, false, true] 4 = true := by decide +kernel
theorem W_w0001011 : Determined [false, false, false, true, false, true, true] 4 = true := by decide +kernel
theorem W_w0001101 : Determined [false, false, false, true, true, false, true] 4 = true := by decide +kernel
theorem W_w0001111 : Determined [false, false, false, true, true, true, true] 4 = true := by decide +kernel
