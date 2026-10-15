import KC.Q01Lanes

/-! Kernel checks for `Q01` at width `56`: chunks `560` to `575` of `1024` (`2 ^ 18` lanes each, `101` levels). -/

namespace KC.Q01W56.C35
open KC.Q01Lanes

theorem c560 : check 56 101 18 560 = true := by decide +kernel
theorem c561 : check 56 101 18 561 = true := by decide +kernel
theorem c562 : check 56 101 18 562 = true := by decide +kernel
theorem c563 : check 56 101 18 563 = true := by decide +kernel
theorem c564 : check 56 101 18 564 = true := by decide +kernel
theorem c565 : check 56 101 18 565 = true := by decide +kernel
theorem c566 : check 56 101 18 566 = true := by decide +kernel
theorem c567 : check 56 101 18 567 = true := by decide +kernel
theorem c568 : check 56 101 18 568 = true := by decide +kernel
theorem c569 : check 56 101 18 569 = true := by decide +kernel
theorem c570 : check 56 101 18 570 = true := by decide +kernel
theorem c571 : check 56 101 18 571 = true := by decide +kernel
theorem c572 : check 56 101 18 572 = true := by decide +kernel
theorem c573 : check 56 101 18 573 = true := by decide +kernel
theorem c574 : check 56 101 18 574 = true := by decide +kernel
theorem c575 : check 56 101 18 575 = true := by decide +kernel

theorem range : ChunksOK 56 101 18 560 16 :=
  (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c560) (chunksOK_one c561)) (chunksOK_append (chunksOK_one c562) (chunksOK_one c563))) (chunksOK_append (chunksOK_append (chunksOK_one c564) (chunksOK_one c565)) (chunksOK_append (chunksOK_one c566) (chunksOK_one c567)))) (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c568) (chunksOK_one c569)) (chunksOK_append (chunksOK_one c570) (chunksOK_one c571))) (chunksOK_append (chunksOK_append (chunksOK_one c572) (chunksOK_one c573)) (chunksOK_append (chunksOK_one c574) (chunksOK_one c575)))))

end KC.Q01W56.C35
