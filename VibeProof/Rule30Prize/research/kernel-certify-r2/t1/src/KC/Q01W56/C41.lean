import KC.Q01Lanes

/-! Kernel checks for `Q01` at width `56`: chunks `656` to `671` of `1024` (`2 ^ 18` lanes each, `101` levels). -/

namespace KC.Q01W56.C41
open KC.Q01Lanes

theorem c656 : check 56 101 18 656 = true := by decide +kernel
theorem c657 : check 56 101 18 657 = true := by decide +kernel
theorem c658 : check 56 101 18 658 = true := by decide +kernel
theorem c659 : check 56 101 18 659 = true := by decide +kernel
theorem c660 : check 56 101 18 660 = true := by decide +kernel
theorem c661 : check 56 101 18 661 = true := by decide +kernel
theorem c662 : check 56 101 18 662 = true := by decide +kernel
theorem c663 : check 56 101 18 663 = true := by decide +kernel
theorem c664 : check 56 101 18 664 = true := by decide +kernel
theorem c665 : check 56 101 18 665 = true := by decide +kernel
theorem c666 : check 56 101 18 666 = true := by decide +kernel
theorem c667 : check 56 101 18 667 = true := by decide +kernel
theorem c668 : check 56 101 18 668 = true := by decide +kernel
theorem c669 : check 56 101 18 669 = true := by decide +kernel
theorem c670 : check 56 101 18 670 = true := by decide +kernel
theorem c671 : check 56 101 18 671 = true := by decide +kernel

theorem range : ChunksOK 56 101 18 656 16 :=
  (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c656) (chunksOK_one c657)) (chunksOK_append (chunksOK_one c658) (chunksOK_one c659))) (chunksOK_append (chunksOK_append (chunksOK_one c660) (chunksOK_one c661)) (chunksOK_append (chunksOK_one c662) (chunksOK_one c663)))) (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c664) (chunksOK_one c665)) (chunksOK_append (chunksOK_one c666) (chunksOK_one c667))) (chunksOK_append (chunksOK_append (chunksOK_one c668) (chunksOK_one c669)) (chunksOK_append (chunksOK_one c670) (chunksOK_one c671)))))

end KC.Q01W56.C41
