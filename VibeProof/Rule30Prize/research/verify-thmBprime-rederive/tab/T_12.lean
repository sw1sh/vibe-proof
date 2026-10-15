import Standalone
open AbsorbRight

theorem T_0001100 : Determined [false, false, false, true, true, false, false] 3 = true := by decide +kernel
theorem T_0001110 : Determined [false, false, false, true, true, true, false] 3 = true := by decide +kernel
