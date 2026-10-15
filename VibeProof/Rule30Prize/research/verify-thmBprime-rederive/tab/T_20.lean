import Standalone
open AbsorbRight

theorem T_0111100 : Determined [false, true, true, true, true, false, false] 3 = true := by decide +kernel
theorem T_0111110 : Determined [false, true, true, true, true, true, false] 3 = true := by decide +kernel
