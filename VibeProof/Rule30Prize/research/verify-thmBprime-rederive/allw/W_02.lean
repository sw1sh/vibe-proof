import Standalone
open AbsorbRight

theorem W_w01 : Determined [false, true] 4 = true := by decide +kernel
theorem W_w10 : Determined [true, false] 4 = true := by decide +kernel
theorem W_w11 : Determined [true, true] 4 = true := by decide +kernel
