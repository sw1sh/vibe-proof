import Standalone
open AbsorbRight

theorem W_w1100000 : Determined [true, true, false, false, false, false, false] 4 = true := by decide +kernel
theorem W_w1100001 : Determined [true, true, false, false, false, false, true] 4 = true := by decide +kernel
theorem W_w1100010 : Determined [true, true, false, false, false, true, false] 4 = true := by decide +kernel
theorem W_w1100011 : Determined [true, true, false, false, false, true, true] 4 = true := by decide +kernel
