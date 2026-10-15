import Standalone
open AbsorbRight

theorem W_w001 : Determined [false, false, true] 4 = true := by decide +kernel
theorem W_w011 : Determined [false, true, true] 4 = true := by decide +kernel
theorem W_w100 : Determined [true, false, false] 4 = true := by decide +kernel
theorem W_w101 : Determined [true, false, true] 4 = true := by decide +kernel
theorem W_w110 : Determined [true, true, false] 4 = true := by decide +kernel
theorem W_w111 : Determined [true, true, true] 4 = true := by decide +kernel
