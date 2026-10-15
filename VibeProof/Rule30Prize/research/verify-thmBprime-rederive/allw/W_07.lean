import Standalone
open AbsorbRight

theorem W_w010001 : Determined [false, true, false, false, false, true] 4 = true := by decide +kernel
theorem W_w010011 : Determined [false, true, false, false, true, true] 4 = true := by decide +kernel
theorem W_w010101 : Determined [false, true, false, true, false, true] 4 = true := by decide +kernel
theorem W_w010111 : Determined [false, true, false, true, true, true] 4 = true := by decide +kernel
theorem W_w011001 : Determined [false, true, true, false, false, true] 4 = true := by decide +kernel
theorem W_w011011 : Determined [false, true, true, false, true, true] 4 = true := by decide +kernel
theorem W_w011101 : Determined [false, true, true, true, false, true] 4 = true := by decide +kernel
theorem W_w011111 : Determined [false, true, true, true, true, true] 4 = true := by decide +kernel
