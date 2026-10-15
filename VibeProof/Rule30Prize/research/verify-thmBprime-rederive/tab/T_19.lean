import Standalone
open AbsorbRight

theorem T_0110100 : Determined [false, true, true, false, true, false, false] 3 = true := by decide +kernel
theorem T_0111010 : Determined [false, true, true, true, false, true, false] 3 = true := by decide +kernel
