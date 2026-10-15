import KC.Q01Lanes

/-! Kernel checks for `Q01` at width `56`: chunks `512` to `527` of `1024` (`2 ^ 18` lanes each, `101` levels). -/

namespace KC.Q01W56.C32
open KC.Q01Lanes

theorem c512 : check 56 101 18 512 = true := by decide +kernel
theorem c513 : check 56 101 18 513 = true := by decide +kernel
theorem c514 : check 56 101 18 514 = true := by decide +kernel
theorem c515 : check 56 101 18 515 = true := by decide +kernel
theorem c516 : check 56 101 18 516 = true := by decide +kernel
theorem c517 : check 56 101 18 517 = true := by decide +kernel
theorem c518 : check 56 101 18 518 = true := by decide +kernel
theorem c519 : check 56 101 18 519 = true := by decide +kernel
theorem c520 : check 56 101 18 520 = true := by decide +kernel
theorem c521 : check 56 101 18 521 = true := by decide +kernel
theorem c522 : check 56 101 18 522 = true := by decide +kernel
theorem c523 : check 56 101 18 523 = true := by decide +kernel
theorem c524 : check 56 101 18 524 = true := by decide +kernel
theorem c525 : check 56 101 18 525 = true := by decide +kernel
theorem c526 : check 56 101 18 526 = true := by decide +kernel
theorem c527 : check 56 101 18 527 = true := by decide +kernel

theorem range : ChunksOK 56 101 18 512 16 :=
  (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c512) (chunksOK_one c513)) (chunksOK_append (chunksOK_one c514) (chunksOK_one c515))) (chunksOK_append (chunksOK_append (chunksOK_one c516) (chunksOK_one c517)) (chunksOK_append (chunksOK_one c518) (chunksOK_one c519)))) (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c520) (chunksOK_one c521)) (chunksOK_append (chunksOK_one c522) (chunksOK_one c523))) (chunksOK_append (chunksOK_append (chunksOK_one c524) (chunksOK_one c525)) (chunksOK_append (chunksOK_one c526) (chunksOK_one c527)))))

end KC.Q01W56.C32
