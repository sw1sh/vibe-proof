import Standalone
open AbsorbRight

theorem T_0011100 : Determined [false, false, true, true, true, false, false] 3 = true := by decide +kernel
theorem T_0011110 : Determined [false, false, true, true, true, true, false] 3 = true := by decide +kernel
