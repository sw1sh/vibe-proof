import Standalone
open AbsorbRight

theorem T_00000 : Determined [false, false, false, false, false] 3 = true := by decide +kernel
theorem T_00010 : Determined [false, false, false, true, false] 3 = true := by decide +kernel
theorem T_00100 : Determined [false, false, true, false, false] 3 = true := by decide +kernel
theorem T_00110 : Determined [false, false, true, true, false] 3 = true := by decide +kernel
theorem T_01000 : Determined [false, true, false, false, false] 3 = true := by decide +kernel
theorem T_01010 : Determined [false, true, false, true, false] 2 = true := by decide +kernel
