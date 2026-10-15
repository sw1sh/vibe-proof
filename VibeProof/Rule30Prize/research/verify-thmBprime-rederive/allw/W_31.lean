import Standalone
open AbsorbRight

theorem W_w1101100 : Determined [true, true, false, true, true, false, false] 4 = true := by decide +kernel
theorem W_w1101101 : Determined [true, true, false, true, true, false, true] 4 = true := by decide +kernel
theorem W_w1101110 : Determined [true, true, false, true, true, true, false] 4 = true := by decide +kernel
theorem W_w1101111 : Determined [true, true, false, true, true, true, true] 4 = true := by decide +kernel
