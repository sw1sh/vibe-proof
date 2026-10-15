import Standalone
open AbsorbRight

theorem T_0000000 : Determined [false, false, false, false, false, false, false] 3 = true := by decide +kernel
theorem T_0000010 : Determined [false, false, false, false, false, true, false] 3 = true := by decide +kernel
