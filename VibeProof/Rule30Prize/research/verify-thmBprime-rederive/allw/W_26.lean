import Standalone
open AbsorbRight

theorem W_w1011000 : Determined [true, false, true, true, false, false, false] 4 = true := by decide +kernel
theorem W_w1011001 : Determined [true, false, true, true, false, false, true] 4 = true := by decide +kernel
theorem W_w1011010 : Determined [true, false, true, true, false, true, false] 4 = true := by decide +kernel
theorem W_w1011011 : Determined [true, false, true, true, false, true, true] 4 = true := by decide +kernel
