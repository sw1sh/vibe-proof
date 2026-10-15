import KC.Q01Lanes

/-! Kernel checks for `Q01` at width `56`: chunks `784` to `799` of `1024` (`2 ^ 18` lanes each, `101` levels). -/

namespace KC.Q01W56.C49
open KC.Q01Lanes

theorem c784 : check 56 101 18 784 = true := by decide +kernel
theorem c785 : check 56 101 18 785 = true := by decide +kernel
theorem c786 : check 56 101 18 786 = true := by decide +kernel
theorem c787 : check 56 101 18 787 = true := by decide +kernel
theorem c788 : check 56 101 18 788 = true := by decide +kernel
theorem c789 : check 56 101 18 789 = true := by decide +kernel
theorem c790 : check 56 101 18 790 = true := by decide +kernel
theorem c791 : check 56 101 18 791 = true := by decide +kernel
theorem c792 : check 56 101 18 792 = true := by decide +kernel
theorem c793 : check 56 101 18 793 = true := by decide +kernel
theorem c794 : check 56 101 18 794 = true := by decide +kernel
theorem c795 : check 56 101 18 795 = true := by decide +kernel
theorem c796 : check 56 101 18 796 = true := by decide +kernel
theorem c797 : check 56 101 18 797 = true := by decide +kernel
theorem c798 : check 56 101 18 798 = true := by decide +kernel
theorem c799 : check 56 101 18 799 = true := by decide +kernel

theorem range : ChunksOK 56 101 18 784 16 :=
  (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c784) (chunksOK_one c785)) (chunksOK_append (chunksOK_one c786) (chunksOK_one c787))) (chunksOK_append (chunksOK_append (chunksOK_one c788) (chunksOK_one c789)) (chunksOK_append (chunksOK_one c790) (chunksOK_one c791)))) (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c792) (chunksOK_one c793)) (chunksOK_append (chunksOK_one c794) (chunksOK_one c795))) (chunksOK_append (chunksOK_append (chunksOK_one c796) (chunksOK_one c797)) (chunksOK_append (chunksOK_one c798) (chunksOK_one c799)))))

end KC.Q01W56.C49
