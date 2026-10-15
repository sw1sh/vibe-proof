import Standalone
open AbsorbRight

theorem W_w1011100 : Determined [true, false, true, true, true, false, false] 4 = true := by decide +kernel
theorem W_w1011101 : Determined [true, false, true, true, true, false, true] 4 = true := by decide +kernel
theorem W_w1011110 : Determined [true, false, true, true, true, true, false] 4 = true := by decide +kernel
theorem W_w1011111 : Determined [true, false, true, true, true, true, true] 4 = true := by decide +kernel
