import KC.Q01Lanes

/-! Kernel checks for `Q01` at width `56`: chunks `480` to `495` of `1024` (`2 ^ 18` lanes each, `101` levels). -/

namespace KC.Q01W56.C30
open KC.Q01Lanes

theorem c480 : check 56 101 18 480 = true := by decide +kernel
theorem c481 : check 56 101 18 481 = true := by decide +kernel
theorem c482 : check 56 101 18 482 = true := by decide +kernel
theorem c483 : check 56 101 18 483 = true := by decide +kernel
theorem c484 : check 56 101 18 484 = true := by decide +kernel
theorem c485 : check 56 101 18 485 = true := by decide +kernel
theorem c486 : check 56 101 18 486 = true := by decide +kernel
theorem c487 : check 56 101 18 487 = true := by decide +kernel
theorem c488 : check 56 101 18 488 = true := by decide +kernel
theorem c489 : check 56 101 18 489 = true := by decide +kernel
theorem c490 : check 56 101 18 490 = true := by decide +kernel
theorem c491 : check 56 101 18 491 = true := by decide +kernel
theorem c492 : check 56 101 18 492 = true := by decide +kernel
theorem c493 : check 56 101 18 493 = true := by decide +kernel
theorem c494 : check 56 101 18 494 = true := by decide +kernel
theorem c495 : check 56 101 18 495 = true := by decide +kernel

theorem range : ChunksOK 56 101 18 480 16 :=
  (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c480) (chunksOK_one c481)) (chunksOK_append (chunksOK_one c482) (chunksOK_one c483))) (chunksOK_append (chunksOK_append (chunksOK_one c484) (chunksOK_one c485)) (chunksOK_append (chunksOK_one c486) (chunksOK_one c487)))) (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c488) (chunksOK_one c489)) (chunksOK_append (chunksOK_one c490) (chunksOK_one c491))) (chunksOK_append (chunksOK_append (chunksOK_one c492) (chunksOK_one c493)) (chunksOK_append (chunksOK_one c494) (chunksOK_one c495)))))

end KC.Q01W56.C30
