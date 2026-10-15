import KC.Q01Lanes

/-! Kernel checks for `Q01` at width `56`: chunks `352` to `367` of `1024` (`2 ^ 18` lanes each, `101` levels). -/

namespace KC.Q01W56.C22
open KC.Q01Lanes

theorem c352 : check 56 101 18 352 = true := by decide +kernel
theorem c353 : check 56 101 18 353 = true := by decide +kernel
theorem c354 : check 56 101 18 354 = true := by decide +kernel
theorem c355 : check 56 101 18 355 = true := by decide +kernel
theorem c356 : check 56 101 18 356 = true := by decide +kernel
theorem c357 : check 56 101 18 357 = true := by decide +kernel
theorem c358 : check 56 101 18 358 = true := by decide +kernel
theorem c359 : check 56 101 18 359 = true := by decide +kernel
theorem c360 : check 56 101 18 360 = true := by decide +kernel
theorem c361 : check 56 101 18 361 = true := by decide +kernel
theorem c362 : check 56 101 18 362 = true := by decide +kernel
theorem c363 : check 56 101 18 363 = true := by decide +kernel
theorem c364 : check 56 101 18 364 = true := by decide +kernel
theorem c365 : check 56 101 18 365 = true := by decide +kernel
theorem c366 : check 56 101 18 366 = true := by decide +kernel
theorem c367 : check 56 101 18 367 = true := by decide +kernel

theorem range : ChunksOK 56 101 18 352 16 :=
  (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c352) (chunksOK_one c353)) (chunksOK_append (chunksOK_one c354) (chunksOK_one c355))) (chunksOK_append (chunksOK_append (chunksOK_one c356) (chunksOK_one c357)) (chunksOK_append (chunksOK_one c358) (chunksOK_one c359)))) (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c360) (chunksOK_one c361)) (chunksOK_append (chunksOK_one c362) (chunksOK_one c363))) (chunksOK_append (chunksOK_append (chunksOK_one c364) (chunksOK_one c365)) (chunksOK_append (chunksOK_one c366) (chunksOK_one c367)))))

end KC.Q01W56.C22
