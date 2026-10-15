import Standalone
open AbsorbRight

theorem T_01100 : Determined [false, true, true, false, false] 2 = true := by decide +kernel
theorem T_01110 : Determined [false, true, true, true, false] 2 = true := by decide +kernel
theorem T_000000 : Determined [false, false, false, false, false, false] 3 = true := by decide +kernel
