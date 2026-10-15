import KC.Q01Lanes

/-! Kernel checks for `Q01` at width `20`: chunks `2` to `3` of `4` (`2 ^ 8` lanes each, `39` levels). -/

namespace KC.Q01W20.C1
open KC.Q01Lanes

theorem c2 : check 20 39 8 2 = true := by decide +kernel
theorem c3 : check 20 39 8 3 = true := by decide +kernel

theorem range : ChunksOK 20 39 8 2 2 :=
  (chunksOK_append (chunksOK_one c2) (chunksOK_one c3))

end KC.Q01W20.C1
