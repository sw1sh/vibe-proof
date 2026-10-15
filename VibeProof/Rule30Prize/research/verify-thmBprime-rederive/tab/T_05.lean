import Standalone
open AbsorbRight

theorem T_001110 : Determined [false, false, true, true, true, false] 3 = true := by decide +kernel
theorem T_010000 : Determined [false, true, false, false, false, false] 3 = true := by decide +kernel
theorem T_010010 : Determined [false, true, false, false, true, false] 3 = true := by decide +kernel
theorem T_010100 : Determined [false, true, false, true, false, false] 3 = true := by decide +kernel
