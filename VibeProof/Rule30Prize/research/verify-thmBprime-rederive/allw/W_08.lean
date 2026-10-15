import Standalone
open AbsorbRight

theorem W_w100000 : Determined [true, false, false, false, false, false] 4 = true := by decide +kernel
theorem W_w100001 : Determined [true, false, false, false, false, true] 4 = true := by decide +kernel
theorem W_w100010 : Determined [true, false, false, false, true, false] 4 = true := by decide +kernel
theorem W_w100011 : Determined [true, false, false, false, true, true] 4 = true := by decide +kernel
theorem W_w100100 : Determined [true, false, false, true, false, false] 4 = true := by decide +kernel
theorem W_w100101 : Determined [true, false, false, true, false, true] 4 = true := by decide +kernel
theorem W_w100110 : Determined [true, false, false, true, true, false] 4 = true := by decide +kernel
theorem W_w100111 : Determined [true, false, false, true, true, true] 4 = true := by decide +kernel
