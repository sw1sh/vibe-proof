import KC.Q01Lanes

/-! Kernel checks for `Q01` at width `56`: chunks `544` to `559` of `1024` (`2 ^ 18` lanes each, `101` levels). -/

namespace KC.Q01W56.C34
open KC.Q01Lanes

theorem c544 : check 56 101 18 544 = true := by decide +kernel
theorem c545 : check 56 101 18 545 = true := by decide +kernel
theorem c546 : check 56 101 18 546 = true := by decide +kernel
theorem c547 : check 56 101 18 547 = true := by decide +kernel
theorem c548 : check 56 101 18 548 = true := by decide +kernel
theorem c549 : check 56 101 18 549 = true := by decide +kernel
theorem c550 : check 56 101 18 550 = true := by decide +kernel
theorem c551 : check 56 101 18 551 = true := by decide +kernel
theorem c552 : check 56 101 18 552 = true := by decide +kernel
theorem c553 : check 56 101 18 553 = true := by decide +kernel
theorem c554 : check 56 101 18 554 = true := by decide +kernel
theorem c555 : check 56 101 18 555 = true := by decide +kernel
theorem c556 : check 56 101 18 556 = true := by decide +kernel
theorem c557 : check 56 101 18 557 = true := by decide +kernel
theorem c558 : check 56 101 18 558 = true := by decide +kernel
theorem c559 : check 56 101 18 559 = true := by decide +kernel

theorem range : ChunksOK 56 101 18 544 16 :=
  (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c544) (chunksOK_one c545)) (chunksOK_append (chunksOK_one c546) (chunksOK_one c547))) (chunksOK_append (chunksOK_append (chunksOK_one c548) (chunksOK_one c549)) (chunksOK_append (chunksOK_one c550) (chunksOK_one c551)))) (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c552) (chunksOK_one c553)) (chunksOK_append (chunksOK_one c554) (chunksOK_one c555))) (chunksOK_append (chunksOK_append (chunksOK_one c556) (chunksOK_one c557)) (chunksOK_append (chunksOK_one c558) (chunksOK_one c559)))))

end KC.Q01W56.C34
