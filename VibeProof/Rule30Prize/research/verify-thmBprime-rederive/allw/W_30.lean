import Standalone
open AbsorbRight

theorem W_w1101000 : Determined [true, true, false, true, false, false, false] 4 = true := by decide +kernel
theorem W_w1101001 : Determined [true, true, false, true, false, false, true] 4 = true := by decide +kernel
theorem W_w1101010 : Determined [true, true, false, true, false, true, false] 4 = true := by decide +kernel
theorem W_w1101011 : Determined [true, true, false, true, false, true, true] 4 = true := by decide +kernel
