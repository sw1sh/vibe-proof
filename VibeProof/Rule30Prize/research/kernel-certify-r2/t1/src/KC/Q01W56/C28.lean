import KC.Q01Lanes

/-! Kernel checks for `Q01` at width `56`: chunks `448` to `463` of `1024` (`2 ^ 18` lanes each, `101` levels). -/

namespace KC.Q01W56.C28
open KC.Q01Lanes

theorem c448 : check 56 101 18 448 = true := by decide +kernel
theorem c449 : check 56 101 18 449 = true := by decide +kernel
theorem c450 : check 56 101 18 450 = true := by decide +kernel
theorem c451 : check 56 101 18 451 = true := by decide +kernel
theorem c452 : check 56 101 18 452 = true := by decide +kernel
theorem c453 : check 56 101 18 453 = true := by decide +kernel
theorem c454 : check 56 101 18 454 = true := by decide +kernel
theorem c455 : check 56 101 18 455 = true := by decide +kernel
theorem c456 : check 56 101 18 456 = true := by decide +kernel
theorem c457 : check 56 101 18 457 = true := by decide +kernel
theorem c458 : check 56 101 18 458 = true := by decide +kernel
theorem c459 : check 56 101 18 459 = true := by decide +kernel
theorem c460 : check 56 101 18 460 = true := by decide +kernel
theorem c461 : check 56 101 18 461 = true := by decide +kernel
theorem c462 : check 56 101 18 462 = true := by decide +kernel
theorem c463 : check 56 101 18 463 = true := by decide +kernel

theorem range : ChunksOK 56 101 18 448 16 :=
  (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c448) (chunksOK_one c449)) (chunksOK_append (chunksOK_one c450) (chunksOK_one c451))) (chunksOK_append (chunksOK_append (chunksOK_one c452) (chunksOK_one c453)) (chunksOK_append (chunksOK_one c454) (chunksOK_one c455)))) (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c456) (chunksOK_one c457)) (chunksOK_append (chunksOK_one c458) (chunksOK_one c459))) (chunksOK_append (chunksOK_append (chunksOK_one c460) (chunksOK_one c461)) (chunksOK_append (chunksOK_one c462) (chunksOK_one c463)))))

end KC.Q01W56.C28
