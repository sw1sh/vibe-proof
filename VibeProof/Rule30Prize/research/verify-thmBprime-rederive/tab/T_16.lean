import Standalone
open AbsorbRight

theorem T_0100000 : Determined [false, true, false, false, false, false, false] 3 = true := by decide +kernel
theorem T_0100010 : Determined [false, true, false, false, false, true, false] 3 = true := by decide +kernel
