import Standalone
open AbsorbRight

theorem W_w0010001 : Determined [false, false, true, false, false, false, true] 4 = true := by decide +kernel
theorem W_w0010011 : Determined [false, false, true, false, false, true, true] 4 = true := by decide +kernel
theorem W_w0010101 : Determined [false, false, true, false, true, false, true] 4 = true := by decide +kernel
theorem W_w0010111 : Determined [false, false, true, false, true, true, true] 4 = true := by decide +kernel
