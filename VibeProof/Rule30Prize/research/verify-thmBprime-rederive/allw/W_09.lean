import Standalone
open AbsorbRight

theorem W_w101000 : Determined [true, false, true, false, false, false] 4 = true := by decide +kernel
theorem W_w101001 : Determined [true, false, true, false, false, true] 4 = true := by decide +kernel
theorem W_w101010 : Determined [true, false, true, false, true, false] 4 = true := by decide +kernel
theorem W_w101011 : Determined [true, false, true, false, true, true] 4 = true := by decide +kernel
theorem W_w101100 : Determined [true, false, true, true, false, false] 4 = true := by decide +kernel
theorem W_w101101 : Determined [true, false, true, true, false, true] 4 = true := by decide +kernel
theorem W_w101110 : Determined [true, false, true, true, true, false] 4 = true := by decide +kernel
theorem W_w101111 : Determined [true, false, true, true, true, true] 4 = true := by decide +kernel
