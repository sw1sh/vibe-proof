import KC.Q01Lanes

/-! Kernel checks for `Q01` at width `56`: chunks `368` to `383` of `1024` (`2 ^ 18` lanes each, `101` levels). -/

namespace KC.Q01W56.C23
open KC.Q01Lanes

theorem c368 : check 56 101 18 368 = true := by decide +kernel
theorem c369 : check 56 101 18 369 = true := by decide +kernel
theorem c370 : check 56 101 18 370 = true := by decide +kernel
theorem c371 : check 56 101 18 371 = true := by decide +kernel
theorem c372 : check 56 101 18 372 = true := by decide +kernel
theorem c373 : check 56 101 18 373 = true := by decide +kernel
theorem c374 : check 56 101 18 374 = true := by decide +kernel
theorem c375 : check 56 101 18 375 = true := by decide +kernel
theorem c376 : check 56 101 18 376 = true := by decide +kernel
theorem c377 : check 56 101 18 377 = true := by decide +kernel
theorem c378 : check 56 101 18 378 = true := by decide +kernel
theorem c379 : check 56 101 18 379 = true := by decide +kernel
theorem c380 : check 56 101 18 380 = true := by decide +kernel
theorem c381 : check 56 101 18 381 = true := by decide +kernel
theorem c382 : check 56 101 18 382 = true := by decide +kernel
theorem c383 : check 56 101 18 383 = true := by decide +kernel

theorem range : ChunksOK 56 101 18 368 16 :=
  (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c368) (chunksOK_one c369)) (chunksOK_append (chunksOK_one c370) (chunksOK_one c371))) (chunksOK_append (chunksOK_append (chunksOK_one c372) (chunksOK_one c373)) (chunksOK_append (chunksOK_one c374) (chunksOK_one c375)))) (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c376) (chunksOK_one c377)) (chunksOK_append (chunksOK_one c378) (chunksOK_one c379))) (chunksOK_append (chunksOK_append (chunksOK_one c380) (chunksOK_one c381)) (chunksOK_append (chunksOK_one c382) (chunksOK_one c383)))))

end KC.Q01W56.C23
