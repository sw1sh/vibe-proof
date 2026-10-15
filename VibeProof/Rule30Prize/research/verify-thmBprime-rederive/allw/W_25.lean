import Standalone
open AbsorbRight

theorem W_w1010100 : Determined [true, false, true, false, true, false, false] 4 = true := by decide +kernel
theorem W_w1010101 : Determined [true, false, true, false, true, false, true] 4 = true := by decide +kernel
theorem W_w1010110 : Determined [true, false, true, false, true, true, false] 4 = true := by decide +kernel
theorem W_w1010111 : Determined [true, false, true, false, true, true, true] 4 = true := by decide +kernel
