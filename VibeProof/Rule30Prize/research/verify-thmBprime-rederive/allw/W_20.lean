import Standalone
open AbsorbRight

theorem W_w1000000 : Determined [true, false, false, false, false, false, false] 4 = true := by decide +kernel
theorem W_w1000001 : Determined [true, false, false, false, false, false, true] 4 = true := by decide +kernel
theorem W_w1000010 : Determined [true, false, false, false, false, true, false] 4 = true := by decide +kernel
theorem W_w1000011 : Determined [true, false, false, false, false, true, true] 4 = true := by decide +kernel
