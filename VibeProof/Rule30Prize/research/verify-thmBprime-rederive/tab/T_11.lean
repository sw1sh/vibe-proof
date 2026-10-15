import Standalone
open AbsorbRight

theorem T_0000110 : Determined [false, false, false, false, true, true, false] 3 = true := by decide +kernel
theorem T_0001010 : Determined [false, false, false, true, false, true, false] 3 = true := by decide +kernel
