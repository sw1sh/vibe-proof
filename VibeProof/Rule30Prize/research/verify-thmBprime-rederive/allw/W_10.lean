import Standalone
open AbsorbRight

theorem W_w110000 : Determined [true, true, false, false, false, false] 4 = true := by decide +kernel
theorem W_w110001 : Determined [true, true, false, false, false, true] 4 = true := by decide +kernel
theorem W_w110010 : Determined [true, true, false, false, true, false] 4 = true := by decide +kernel
theorem W_w110011 : Determined [true, true, false, false, true, true] 4 = true := by decide +kernel
theorem W_w110100 : Determined [true, true, false, true, false, false] 4 = true := by decide +kernel
theorem W_w110101 : Determined [true, true, false, true, false, true] 4 = true := by decide +kernel
theorem W_w110110 : Determined [true, true, false, true, true, false] 4 = true := by decide +kernel
theorem W_w110111 : Determined [true, true, false, true, true, true] 4 = true := by decide +kernel
