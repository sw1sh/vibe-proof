import Standalone
open AbsorbRight

theorem W_w0100001 : Determined [false, true, false, false, false, false, true] 4 = true := by decide +kernel
theorem W_w0100011 : Determined [false, true, false, false, false, true, true] 4 = true := by decide +kernel
theorem W_w0100101 : Determined [false, true, false, false, true, false, true] 4 = true := by decide +kernel
theorem W_w0100111 : Determined [false, true, false, false, true, true, true] 4 = true := by decide +kernel
