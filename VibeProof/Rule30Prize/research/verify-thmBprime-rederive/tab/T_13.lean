import Standalone
open AbsorbRight

theorem T_0010000 : Determined [false, false, true, false, false, false, false] 3 = true := by decide +kernel
theorem T_0010100 : Determined [false, false, true, false, true, false, false] 3 = true := by decide +kernel
