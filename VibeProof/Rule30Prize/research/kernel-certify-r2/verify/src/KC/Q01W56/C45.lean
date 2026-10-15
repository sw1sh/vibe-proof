import KC.Q01Lanes

/-! Kernel checks for `Q01` at width `56`: chunks `720` to `735` of `1024` (`2 ^ 18` lanes each, `101` levels). -/

namespace KC.Q01W56.C45
open KC.Q01Lanes

theorem c720 : check 56 101 18 720 = true := by decide +kernel
theorem c721 : check 56 101 18 721 = true := by decide +kernel
theorem c722 : check 56 101 18 722 = true := by decide +kernel
theorem c723 : check 56 101 18 723 = true := by decide +kernel
theorem c724 : check 56 101 18 724 = true := by decide +kernel
theorem c725 : check 56 101 18 725 = true := by decide +kernel
theorem c726 : check 56 101 18 726 = true := by decide +kernel
theorem c727 : check 56 101 18 727 = true := by decide +kernel
theorem c728 : check 56 101 18 728 = true := by decide +kernel
theorem c729 : check 56 101 18 729 = true := by decide +kernel
theorem c730 : check 56 101 18 730 = true := by decide +kernel
theorem c731 : check 56 101 18 731 = true := by decide +kernel
theorem c732 : check 56 101 18 732 = true := by decide +kernel
theorem c733 : check 56 101 18 733 = true := by decide +kernel
theorem c734 : check 56 101 18 734 = true := by decide +kernel
theorem c735 : check 56 101 18 735 = true := by decide +kernel

theorem range : ChunksOK 56 101 18 720 16 :=
  (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c720) (chunksOK_one c721)) (chunksOK_append (chunksOK_one c722) (chunksOK_one c723))) (chunksOK_append (chunksOK_append (chunksOK_one c724) (chunksOK_one c725)) (chunksOK_append (chunksOK_one c726) (chunksOK_one c727)))) (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c728) (chunksOK_one c729)) (chunksOK_append (chunksOK_one c730) (chunksOK_one c731))) (chunksOK_append (chunksOK_append (chunksOK_one c732) (chunksOK_one c733)) (chunksOK_append (chunksOK_one c734) (chunksOK_one c735)))))

end KC.Q01W56.C45
