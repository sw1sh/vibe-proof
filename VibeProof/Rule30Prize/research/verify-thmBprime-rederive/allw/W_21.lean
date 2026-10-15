import Standalone
open AbsorbRight

theorem W_w1000100 : Determined [true, false, false, false, true, false, false] 4 = true := by decide +kernel
theorem W_w1000101 : Determined [true, false, false, false, true, false, true] 4 = true := by decide +kernel
theorem W_w1000110 : Determined [true, false, false, false, true, true, false] 4 = true := by decide +kernel
theorem W_w1000111 : Determined [true, false, false, false, true, true, true] 4 = true := by decide +kernel
