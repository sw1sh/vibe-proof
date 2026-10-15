import Standalone
open AbsorbRight

theorem W_w1110100 : Determined [true, true, true, false, true, false, false] 4 = true := by decide +kernel
theorem W_w1110101 : Determined [true, true, true, false, true, false, true] 4 = true := by decide +kernel
theorem W_w1110110 : Determined [true, true, true, false, true, true, false] 4 = true := by decide +kernel
theorem W_w1110111 : Determined [true, true, true, false, true, true, true] 4 = true := by decide +kernel
