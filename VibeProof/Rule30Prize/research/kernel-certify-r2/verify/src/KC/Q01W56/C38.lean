import KC.Q01Lanes

/-! Kernel checks for `Q01` at width `56`: chunks `608` to `623` of `1024` (`2 ^ 18` lanes each, `101` levels). -/

namespace KC.Q01W56.C38
open KC.Q01Lanes

theorem c608 : check 56 101 18 608 = true := by decide +kernel
theorem c609 : check 56 101 18 609 = true := by decide +kernel
theorem c610 : check 56 101 18 610 = true := by decide +kernel
theorem c611 : check 56 101 18 611 = true := by decide +kernel
theorem c612 : check 56 101 18 612 = true := by decide +kernel
theorem c613 : check 56 101 18 613 = true := by decide +kernel
theorem c614 : check 56 101 18 614 = true := by decide +kernel
theorem c615 : check 56 101 18 615 = true := by decide +kernel
theorem c616 : check 56 101 18 616 = true := by decide +kernel
theorem c617 : check 56 101 18 617 = true := by decide +kernel
theorem c618 : check 56 101 18 618 = true := by decide +kernel
theorem c619 : check 56 101 18 619 = true := by decide +kernel
theorem c620 : check 56 101 18 620 = true := by decide +kernel
theorem c621 : check 56 101 18 621 = true := by decide +kernel
theorem c622 : check 56 101 18 622 = true := by decide +kernel
theorem c623 : check 56 101 18 623 = true := by decide +kernel

theorem range : ChunksOK 56 101 18 608 16 :=
  (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c608) (chunksOK_one c609)) (chunksOK_append (chunksOK_one c610) (chunksOK_one c611))) (chunksOK_append (chunksOK_append (chunksOK_one c612) (chunksOK_one c613)) (chunksOK_append (chunksOK_one c614) (chunksOK_one c615)))) (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c616) (chunksOK_one c617)) (chunksOK_append (chunksOK_one c618) (chunksOK_one c619))) (chunksOK_append (chunksOK_append (chunksOK_one c620) (chunksOK_one c621)) (chunksOK_append (chunksOK_one c622) (chunksOK_one c623)))))

end KC.Q01W56.C38
