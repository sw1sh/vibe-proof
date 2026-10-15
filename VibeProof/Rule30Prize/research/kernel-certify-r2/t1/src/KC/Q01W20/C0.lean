import KC.Q01Lanes

/-! Kernel checks for `Q01` at width `20`: chunks `0` to `1` of `4` (`2 ^ 8` lanes each, `39` levels). -/

namespace KC.Q01W20.C0
open KC.Q01Lanes

theorem c0 : check 20 39 8 0 = true := by decide +kernel
theorem c1 : check 20 39 8 1 = true := by decide +kernel

theorem range : ChunksOK 20 39 8 0 2 :=
  (chunksOK_append (chunksOK_one c0) (chunksOK_one c1))

end KC.Q01W20.C0
