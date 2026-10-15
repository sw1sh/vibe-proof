import KC.Q01Lanes

/-! Kernel checks for `Q01` at width `56`: chunks `528` to `543` of `1024` (`2 ^ 18` lanes each, `101` levels). -/

namespace KC.Q01W56.C33
open KC.Q01Lanes

theorem c528 : check 56 101 18 528 = true := by decide +kernel
theorem c529 : check 56 101 18 529 = true := by decide +kernel
theorem c530 : check 56 101 18 530 = true := by decide +kernel
theorem c531 : check 56 101 18 531 = true := by decide +kernel
theorem c532 : check 56 101 18 532 = true := by decide +kernel
theorem c533 : check 56 101 18 533 = true := by decide +kernel
theorem c534 : check 56 101 18 534 = true := by decide +kernel
theorem c535 : check 56 101 18 535 = true := by decide +kernel
theorem c536 : check 56 101 18 536 = true := by decide +kernel
theorem c537 : check 56 101 18 537 = true := by decide +kernel
theorem c538 : check 56 101 18 538 = true := by decide +kernel
theorem c539 : check 56 101 18 539 = true := by decide +kernel
theorem c540 : check 56 101 18 540 = true := by decide +kernel
theorem c541 : check 56 101 18 541 = true := by decide +kernel
theorem c542 : check 56 101 18 542 = true := by decide +kernel
theorem c543 : check 56 101 18 543 = true := by decide +kernel

theorem range : ChunksOK 56 101 18 528 16 :=
  (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c528) (chunksOK_one c529)) (chunksOK_append (chunksOK_one c530) (chunksOK_one c531))) (chunksOK_append (chunksOK_append (chunksOK_one c532) (chunksOK_one c533)) (chunksOK_append (chunksOK_one c534) (chunksOK_one c535)))) (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c536) (chunksOK_one c537)) (chunksOK_append (chunksOK_one c538) (chunksOK_one c539))) (chunksOK_append (chunksOK_append (chunksOK_one c540) (chunksOK_one c541)) (chunksOK_append (chunksOK_one c542) (chunksOK_one c543)))))

end KC.Q01W56.C33
