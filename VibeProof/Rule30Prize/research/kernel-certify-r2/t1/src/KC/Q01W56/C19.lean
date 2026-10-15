import KC.Q01Lanes

/-! Kernel checks for `Q01` at width `56`: chunks `304` to `319` of `1024` (`2 ^ 18` lanes each, `101` levels). -/

namespace KC.Q01W56.C19
open KC.Q01Lanes

theorem c304 : check 56 101 18 304 = true := by decide +kernel
theorem c305 : check 56 101 18 305 = true := by decide +kernel
theorem c306 : check 56 101 18 306 = true := by decide +kernel
theorem c307 : check 56 101 18 307 = true := by decide +kernel
theorem c308 : check 56 101 18 308 = true := by decide +kernel
theorem c309 : check 56 101 18 309 = true := by decide +kernel
theorem c310 : check 56 101 18 310 = true := by decide +kernel
theorem c311 : check 56 101 18 311 = true := by decide +kernel
theorem c312 : check 56 101 18 312 = true := by decide +kernel
theorem c313 : check 56 101 18 313 = true := by decide +kernel
theorem c314 : check 56 101 18 314 = true := by decide +kernel
theorem c315 : check 56 101 18 315 = true := by decide +kernel
theorem c316 : check 56 101 18 316 = true := by decide +kernel
theorem c317 : check 56 101 18 317 = true := by decide +kernel
theorem c318 : check 56 101 18 318 = true := by decide +kernel
theorem c319 : check 56 101 18 319 = true := by decide +kernel

theorem range : ChunksOK 56 101 18 304 16 :=
  (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c304) (chunksOK_one c305)) (chunksOK_append (chunksOK_one c306) (chunksOK_one c307))) (chunksOK_append (chunksOK_append (chunksOK_one c308) (chunksOK_one c309)) (chunksOK_append (chunksOK_one c310) (chunksOK_one c311)))) (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c312) (chunksOK_one c313)) (chunksOK_append (chunksOK_one c314) (chunksOK_one c315))) (chunksOK_append (chunksOK_append (chunksOK_one c316) (chunksOK_one c317)) (chunksOK_append (chunksOK_one c318) (chunksOK_one c319)))))

end KC.Q01W56.C19
