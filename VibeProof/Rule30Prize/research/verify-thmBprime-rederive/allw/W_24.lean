import Standalone
open AbsorbRight

theorem W_w1010000 : Determined [true, false, true, false, false, false, false] 4 = true := by decide +kernel
theorem W_w1010001 : Determined [true, false, true, false, false, false, true] 4 = true := by decide +kernel
theorem W_w1010010 : Determined [true, false, true, false, false, true, false] 4 = true := by decide +kernel
theorem W_w1010011 : Determined [true, false, true, false, false, true, true] 4 = true := by decide +kernel
