import Standalone
open AbsorbRight

theorem W_w0110001 : Determined [false, true, true, false, false, false, true] 4 = true := by decide +kernel
theorem W_w0110011 : Determined [false, true, true, false, false, true, true] 4 = true := by decide +kernel
theorem W_w0110101 : Determined [false, true, true, false, true, false, true] 4 = true := by decide +kernel
theorem W_w0110111 : Determined [false, true, true, false, true, true, true] 4 = true := by decide +kernel
