import KC.Q01Lanes

/-! Kernel checks for `Q01` at width `56`: chunks `464` to `479` of `1024` (`2 ^ 18` lanes each, `101` levels). -/

namespace KC.Q01W56.C29
open KC.Q01Lanes

theorem c464 : check 56 101 18 464 = true := by decide +kernel
theorem c465 : check 56 101 18 465 = true := by decide +kernel
theorem c466 : check 56 101 18 466 = true := by decide +kernel
theorem c467 : check 56 101 18 467 = true := by decide +kernel
theorem c468 : check 56 101 18 468 = true := by decide +kernel
theorem c469 : check 56 101 18 469 = true := by decide +kernel
theorem c470 : check 56 101 18 470 = true := by decide +kernel
theorem c471 : check 56 101 18 471 = true := by decide +kernel
theorem c472 : check 56 101 18 472 = true := by decide +kernel
theorem c473 : check 56 101 18 473 = true := by decide +kernel
theorem c474 : check 56 101 18 474 = true := by decide +kernel
theorem c475 : check 56 101 18 475 = true := by decide +kernel
theorem c476 : check 56 101 18 476 = true := by decide +kernel
theorem c477 : check 56 101 18 477 = true := by decide +kernel
theorem c478 : check 56 101 18 478 = true := by decide +kernel
theorem c479 : check 56 101 18 479 = true := by decide +kernel

theorem range : ChunksOK 56 101 18 464 16 :=
  (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c464) (chunksOK_one c465)) (chunksOK_append (chunksOK_one c466) (chunksOK_one c467))) (chunksOK_append (chunksOK_append (chunksOK_one c468) (chunksOK_one c469)) (chunksOK_append (chunksOK_one c470) (chunksOK_one c471)))) (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c472) (chunksOK_one c473)) (chunksOK_append (chunksOK_one c474) (chunksOK_one c475))) (chunksOK_append (chunksOK_append (chunksOK_one c476) (chunksOK_one c477)) (chunksOK_append (chunksOK_one c478) (chunksOK_one c479)))))

end KC.Q01W56.C29
