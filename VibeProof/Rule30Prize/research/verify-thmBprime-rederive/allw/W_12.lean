import Standalone
open AbsorbRight

theorem W_w0000001 : Determined [false, false, false, false, false, false, true] 4 = true := by decide +kernel
theorem W_w0000011 : Determined [false, false, false, false, false, true, true] 4 = true := by decide +kernel
theorem W_w0000101 : Determined [false, false, false, false, true, false, true] 4 = true := by decide +kernel
theorem W_w0000111 : Determined [false, false, false, false, true, true, true] 4 = true := by decide +kernel
