import Standalone
open AbsorbRight

theorem W_w0101001 : Determined [false, true, false, true, false, false, true] 4 = true := by decide +kernel
theorem W_w0101011 : Determined [false, true, false, true, false, true, true] 4 = true := by decide +kernel
theorem W_w0101101 : Determined [false, true, false, true, true, false, true] 4 = true := by decide +kernel
theorem W_w0101111 : Determined [false, true, false, true, true, true, true] 4 = true := by decide +kernel
