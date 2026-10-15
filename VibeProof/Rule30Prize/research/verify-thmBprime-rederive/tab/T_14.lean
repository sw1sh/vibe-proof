import Standalone
open AbsorbRight

theorem T_0011000 : Determined [false, false, true, true, false, false, false] 3 = true := by decide +kernel
theorem T_0011010 : Determined [false, false, true, true, false, true, false] 3 = true := by decide +kernel
