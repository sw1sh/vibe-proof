import Standalone
open AbsorbRight

theorem T_0100110 : Determined [false, true, false, false, true, true, false] 3 = true := by decide +kernel
theorem T_0101010 : Determined [false, true, false, true, false, true, false] 3 = true := by decide +kernel
