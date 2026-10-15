import Standalone
open AbsorbRight

theorem W_w00001 : Determined [false, false, false, false, true] 4 = true := by decide +kernel
theorem W_w00011 : Determined [false, false, false, true, true] 4 = true := by decide +kernel
theorem W_w00101 : Determined [false, false, true, false, true] 4 = true := by decide +kernel
theorem W_w00111 : Determined [false, false, true, true, true] 4 = true := by decide +kernel
theorem W_w01001 : Determined [false, true, false, false, true] 4 = true := by decide +kernel
theorem W_w01011 : Determined [false, true, false, true, true] 4 = true := by decide +kernel
theorem W_w01101 : Determined [false, true, true, false, true] 4 = true := by decide +kernel
theorem W_w01111 : Determined [false, true, true, true, true] 4 = true := by decide +kernel
theorem W_w10000 : Determined [true, false, false, false, false] 4 = true := by decide +kernel
theorem W_w10001 : Determined [true, false, false, false, true] 4 = true := by decide +kernel
theorem W_w10010 : Determined [true, false, false, true, false] 4 = true := by decide +kernel
theorem W_w10011 : Determined [true, false, false, true, true] 4 = true := by decide +kernel
theorem W_w10100 : Determined [true, false, true, false, false] 4 = true := by decide +kernel
theorem W_w10101 : Determined [true, false, true, false, true] 4 = true := by decide +kernel
theorem W_w10110 : Determined [true, false, true, true, false] 4 = true := by decide +kernel
theorem W_w10111 : Determined [true, false, true, true, true] 4 = true := by decide +kernel
theorem W_w11000 : Determined [true, true, false, false, false] 4 = true := by decide +kernel
theorem W_w11001 : Determined [true, true, false, false, true] 4 = true := by decide +kernel
theorem W_w11010 : Determined [true, true, false, true, false] 4 = true := by decide +kernel
theorem W_w11011 : Determined [true, true, false, true, true] 4 = true := by decide +kernel
theorem W_w11100 : Determined [true, true, true, false, false] 4 = true := by decide +kernel
theorem W_w11101 : Determined [true, true, true, false, true] 4 = true := by decide +kernel
theorem W_w11110 : Determined [true, true, true, true, false] 4 = true := by decide +kernel
theorem W_w11111 : Determined [true, true, true, true, true] 4 = true := by decide +kernel
