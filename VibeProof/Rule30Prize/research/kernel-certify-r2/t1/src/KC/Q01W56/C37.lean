import KC.Q01Lanes

/-! Kernel checks for `Q01` at width `56`: chunks `592` to `607` of `1024` (`2 ^ 18` lanes each, `101` levels). -/

namespace KC.Q01W56.C37
open KC.Q01Lanes

theorem c592 : check 56 101 18 592 = true := by decide +kernel
theorem c593 : check 56 101 18 593 = true := by decide +kernel
theorem c594 : check 56 101 18 594 = true := by decide +kernel
theorem c595 : check 56 101 18 595 = true := by decide +kernel
theorem c596 : check 56 101 18 596 = true := by decide +kernel
theorem c597 : check 56 101 18 597 = true := by decide +kernel
theorem c598 : check 56 101 18 598 = true := by decide +kernel
theorem c599 : check 56 101 18 599 = true := by decide +kernel
theorem c600 : check 56 101 18 600 = true := by decide +kernel
theorem c601 : check 56 101 18 601 = true := by decide +kernel
theorem c602 : check 56 101 18 602 = true := by decide +kernel
theorem c603 : check 56 101 18 603 = true := by decide +kernel
theorem c604 : check 56 101 18 604 = true := by decide +kernel
theorem c605 : check 56 101 18 605 = true := by decide +kernel
theorem c606 : check 56 101 18 606 = true := by decide +kernel
theorem c607 : check 56 101 18 607 = true := by decide +kernel

theorem range : ChunksOK 56 101 18 592 16 :=
  (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c592) (chunksOK_one c593)) (chunksOK_append (chunksOK_one c594) (chunksOK_one c595))) (chunksOK_append (chunksOK_append (chunksOK_one c596) (chunksOK_one c597)) (chunksOK_append (chunksOK_one c598) (chunksOK_one c599)))) (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c600) (chunksOK_one c601)) (chunksOK_append (chunksOK_one c602) (chunksOK_one c603))) (chunksOK_append (chunksOK_append (chunksOK_one c604) (chunksOK_one c605)) (chunksOK_append (chunksOK_one c606) (chunksOK_one c607)))))

end KC.Q01W56.C37
