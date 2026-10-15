import KC.Q01Lanes

/-! Kernel checks for `Q01` at width `56`: chunks `336` to `351` of `1024` (`2 ^ 18` lanes each, `101` levels). -/

namespace KC.Q01W56.C21
open KC.Q01Lanes

theorem c336 : check 56 101 18 336 = true := by decide +kernel
theorem c337 : check 56 101 18 337 = true := by decide +kernel
theorem c338 : check 56 101 18 338 = true := by decide +kernel
theorem c339 : check 56 101 18 339 = true := by decide +kernel
theorem c340 : check 56 101 18 340 = true := by decide +kernel
theorem c341 : check 56 101 18 341 = true := by decide +kernel
theorem c342 : check 56 101 18 342 = true := by decide +kernel
theorem c343 : check 56 101 18 343 = true := by decide +kernel
theorem c344 : check 56 101 18 344 = true := by decide +kernel
theorem c345 : check 56 101 18 345 = true := by decide +kernel
theorem c346 : check 56 101 18 346 = true := by decide +kernel
theorem c347 : check 56 101 18 347 = true := by decide +kernel
theorem c348 : check 56 101 18 348 = true := by decide +kernel
theorem c349 : check 56 101 18 349 = true := by decide +kernel
theorem c350 : check 56 101 18 350 = true := by decide +kernel
theorem c351 : check 56 101 18 351 = true := by decide +kernel

theorem range : ChunksOK 56 101 18 336 16 :=
  (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c336) (chunksOK_one c337)) (chunksOK_append (chunksOK_one c338) (chunksOK_one c339))) (chunksOK_append (chunksOK_append (chunksOK_one c340) (chunksOK_one c341)) (chunksOK_append (chunksOK_one c342) (chunksOK_one c343)))) (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c344) (chunksOK_one c345)) (chunksOK_append (chunksOK_one c346) (chunksOK_one c347))) (chunksOK_append (chunksOK_append (chunksOK_one c348) (chunksOK_one c349)) (chunksOK_append (chunksOK_one c350) (chunksOK_one c351)))))

end KC.Q01W56.C21
