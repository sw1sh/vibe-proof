import KC.Q01Lanes

/-! Kernel checks for `Q01` at width `56`: chunks `256` to `271` of `1024` (`2 ^ 18` lanes each, `101` levels). -/

namespace KC.Q01W56.C16
open KC.Q01Lanes

theorem c256 : check 56 101 18 256 = true := by decide +kernel
theorem c257 : check 56 101 18 257 = true := by decide +kernel
theorem c258 : check 56 101 18 258 = true := by decide +kernel
theorem c259 : check 56 101 18 259 = true := by decide +kernel
theorem c260 : check 56 101 18 260 = true := by decide +kernel
theorem c261 : check 56 101 18 261 = true := by decide +kernel
theorem c262 : check 56 101 18 262 = true := by decide +kernel
theorem c263 : check 56 101 18 263 = true := by decide +kernel
theorem c264 : check 56 101 18 264 = true := by decide +kernel
theorem c265 : check 56 101 18 265 = true := by decide +kernel
theorem c266 : check 56 101 18 266 = true := by decide +kernel
theorem c267 : check 56 101 18 267 = true := by decide +kernel
theorem c268 : check 56 101 18 268 = true := by decide +kernel
theorem c269 : check 56 101 18 269 = true := by decide +kernel
theorem c270 : check 56 101 18 270 = true := by decide +kernel
theorem c271 : check 56 101 18 271 = true := by decide +kernel

theorem range : ChunksOK 56 101 18 256 16 :=
  (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c256) (chunksOK_one c257)) (chunksOK_append (chunksOK_one c258) (chunksOK_one c259))) (chunksOK_append (chunksOK_append (chunksOK_one c260) (chunksOK_one c261)) (chunksOK_append (chunksOK_one c262) (chunksOK_one c263)))) (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c264) (chunksOK_one c265)) (chunksOK_append (chunksOK_one c266) (chunksOK_one c267))) (chunksOK_append (chunksOK_append (chunksOK_one c268) (chunksOK_one c269)) (chunksOK_append (chunksOK_one c270) (chunksOK_one c271)))))

end KC.Q01W56.C16
