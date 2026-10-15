import Standalone
open AbsorbRight

theorem W_w1100100 : Determined [true, true, false, false, true, false, false] 4 = true := by decide +kernel
theorem W_w1100101 : Determined [true, true, false, false, true, false, true] 4 = true := by decide +kernel
theorem W_w1100110 : Determined [true, true, false, false, true, true, false] 4 = true := by decide +kernel
theorem W_w1100111 : Determined [true, true, false, false, true, true, true] 4 = true := by decide +kernel
