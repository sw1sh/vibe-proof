import Standalone
open AbsorbRight

theorem W_w1001100 : Determined [true, false, false, true, true, false, false] 4 = true := by decide +kernel
theorem W_w1001101 : Determined [true, false, false, true, true, false, true] 4 = true := by decide +kernel
theorem W_w1001110 : Determined [true, false, false, true, true, true, false] 4 = true := by decide +kernel
theorem W_w1001111 : Determined [true, false, false, true, true, true, true] 4 = true := by decide +kernel
