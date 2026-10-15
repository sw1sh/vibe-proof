import Standalone
open AbsorbRight

theorem W_w000001 : Determined [false, false, false, false, false, true] 4 = true := by decide +kernel
theorem W_w000011 : Determined [false, false, false, false, true, true] 4 = true := by decide +kernel
theorem W_w000101 : Determined [false, false, false, true, false, true] 4 = true := by decide +kernel
theorem W_w000111 : Determined [false, false, false, true, true, true] 4 = true := by decide +kernel
theorem W_w001001 : Determined [false, false, true, false, false, true] 4 = true := by decide +kernel
theorem W_w001011 : Determined [false, false, true, false, true, true] 4 = true := by decide +kernel
theorem W_w001101 : Determined [false, false, true, true, false, true] 4 = true := by decide +kernel
theorem W_w001111 : Determined [false, false, true, true, true, true] 4 = true := by decide +kernel
