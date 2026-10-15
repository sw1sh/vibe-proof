import Standalone
open AbsorbRight

theorem T_000010 : Determined [false, false, false, false, true, false] 3 = true := by decide +kernel
theorem T_000100 : Determined [false, false, false, true, false, false] 3 = true := by decide +kernel
theorem T_000110 : Determined [false, false, false, true, true, false] 3 = true := by decide +kernel
theorem T_001000 : Determined [false, false, true, false, false, false] 3 = true := by decide +kernel
