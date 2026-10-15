import KC.Q01Lanes

/-! Kernel checks for `Q01` at width `56`: chunks `288` to `303` of `1024` (`2 ^ 18` lanes each, `101` levels). -/

namespace KC.Q01W56.C18
open KC.Q01Lanes

theorem c288 : check 56 101 18 288 = true := by decide +kernel
theorem c289 : check 56 101 18 289 = true := by decide +kernel
theorem c290 : check 56 101 18 290 = true := by decide +kernel
theorem c291 : check 56 101 18 291 = true := by decide +kernel
theorem c292 : check 56 101 18 292 = true := by decide +kernel
theorem c293 : check 56 101 18 293 = true := by decide +kernel
theorem c294 : check 56 101 18 294 = true := by decide +kernel
theorem c295 : check 56 101 18 295 = true := by decide +kernel
theorem c296 : check 56 101 18 296 = true := by decide +kernel
theorem c297 : check 56 101 18 297 = true := by decide +kernel
theorem c298 : check 56 101 18 298 = true := by decide +kernel
theorem c299 : check 56 101 18 299 = true := by decide +kernel
theorem c300 : check 56 101 18 300 = true := by decide +kernel
theorem c301 : check 56 101 18 301 = true := by decide +kernel
theorem c302 : check 56 101 18 302 = true := by decide +kernel
theorem c303 : check 56 101 18 303 = true := by decide +kernel

theorem range : ChunksOK 56 101 18 288 16 :=
  (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c288) (chunksOK_one c289)) (chunksOK_append (chunksOK_one c290) (chunksOK_one c291))) (chunksOK_append (chunksOK_append (chunksOK_one c292) (chunksOK_one c293)) (chunksOK_append (chunksOK_one c294) (chunksOK_one c295)))) (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c296) (chunksOK_one c297)) (chunksOK_append (chunksOK_one c298) (chunksOK_one c299))) (chunksOK_append (chunksOK_append (chunksOK_one c300) (chunksOK_one c301)) (chunksOK_append (chunksOK_one c302) (chunksOK_one c303)))))

end KC.Q01W56.C18
