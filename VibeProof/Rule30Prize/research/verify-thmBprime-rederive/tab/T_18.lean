import Standalone
open AbsorbRight

theorem T_0101100 : Determined [false, true, false, true, true, false, false] 3 = true := by decide +kernel
theorem T_0101110 : Determined [false, true, false, true, true, true, false] 3 = true := by decide +kernel
