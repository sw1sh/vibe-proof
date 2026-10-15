import KC.Q01Lanes

/-! Kernel checks for `Q01` at width `56`: chunks `688` to `703` of `1024` (`2 ^ 18` lanes each, `101` levels). -/

namespace KC.Q01W56.C43
open KC.Q01Lanes

theorem c688 : check 56 101 18 688 = true := by decide +kernel
theorem c689 : check 56 101 18 689 = true := by decide +kernel
theorem c690 : check 56 101 18 690 = true := by decide +kernel
theorem c691 : check 56 101 18 691 = true := by decide +kernel
theorem c692 : check 56 101 18 692 = true := by decide +kernel
theorem c693 : check 56 101 18 693 = true := by decide +kernel
theorem c694 : check 56 101 18 694 = true := by decide +kernel
theorem c695 : check 56 101 18 695 = true := by decide +kernel
theorem c696 : check 56 101 18 696 = true := by decide +kernel
theorem c697 : check 56 101 18 697 = true := by decide +kernel
theorem c698 : check 56 101 18 698 = true := by decide +kernel
theorem c699 : check 56 101 18 699 = true := by decide +kernel
theorem c700 : check 56 101 18 700 = true := by decide +kernel
theorem c701 : check 56 101 18 701 = true := by decide +kernel
theorem c702 : check 56 101 18 702 = true := by decide +kernel
theorem c703 : check 56 101 18 703 = true := by decide +kernel

theorem range : ChunksOK 56 101 18 688 16 :=
  (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c688) (chunksOK_one c689)) (chunksOK_append (chunksOK_one c690) (chunksOK_one c691))) (chunksOK_append (chunksOK_append (chunksOK_one c692) (chunksOK_one c693)) (chunksOK_append (chunksOK_one c694) (chunksOK_one c695)))) (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c696) (chunksOK_one c697)) (chunksOK_append (chunksOK_one c698) (chunksOK_one c699))) (chunksOK_append (chunksOK_append (chunksOK_one c700) (chunksOK_one c701)) (chunksOK_append (chunksOK_one c702) (chunksOK_one c703)))))

end KC.Q01W56.C43
