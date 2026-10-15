import KC.Q01Lanes

/-! Kernel checks for `Q01` at width `56`: chunks `752` to `767` of `1024` (`2 ^ 18` lanes each, `101` levels). -/

namespace KC.Q01W56.C47
open KC.Q01Lanes

theorem c752 : check 56 101 18 752 = true := by decide +kernel
theorem c753 : check 56 101 18 753 = true := by decide +kernel
theorem c754 : check 56 101 18 754 = true := by decide +kernel
theorem c755 : check 56 101 18 755 = true := by decide +kernel
theorem c756 : check 56 101 18 756 = true := by decide +kernel
theorem c757 : check 56 101 18 757 = true := by decide +kernel
theorem c758 : check 56 101 18 758 = true := by decide +kernel
theorem c759 : check 56 101 18 759 = true := by decide +kernel
theorem c760 : check 56 101 18 760 = true := by decide +kernel
theorem c761 : check 56 101 18 761 = true := by decide +kernel
theorem c762 : check 56 101 18 762 = true := by decide +kernel
theorem c763 : check 56 101 18 763 = true := by decide +kernel
theorem c764 : check 56 101 18 764 = true := by decide +kernel
theorem c765 : check 56 101 18 765 = true := by decide +kernel
theorem c766 : check 56 101 18 766 = true := by decide +kernel
theorem c767 : check 56 101 18 767 = true := by decide +kernel

theorem range : ChunksOK 56 101 18 752 16 :=
  (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c752) (chunksOK_one c753)) (chunksOK_append (chunksOK_one c754) (chunksOK_one c755))) (chunksOK_append (chunksOK_append (chunksOK_one c756) (chunksOK_one c757)) (chunksOK_append (chunksOK_one c758) (chunksOK_one c759)))) (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c760) (chunksOK_one c761)) (chunksOK_append (chunksOK_one c762) (chunksOK_one c763))) (chunksOK_append (chunksOK_append (chunksOK_one c764) (chunksOK_one c765)) (chunksOK_append (chunksOK_one c766) (chunksOK_one c767)))))

end KC.Q01W56.C47
