import KC.Q01Lanes

/-! Kernel checks for `Q01` at width `56`: chunks `912` to `927` of `1024` (`2 ^ 18` lanes each, `101` levels). -/

namespace KC.Q01W56.C57
open KC.Q01Lanes

theorem c912 : check 56 101 18 912 = true := by decide +kernel
theorem c913 : check 56 101 18 913 = true := by decide +kernel
theorem c914 : check 56 101 18 914 = true := by decide +kernel
theorem c915 : check 56 101 18 915 = true := by decide +kernel
theorem c916 : check 56 101 18 916 = true := by decide +kernel
theorem c917 : check 56 101 18 917 = true := by decide +kernel
theorem c918 : check 56 101 18 918 = true := by decide +kernel
theorem c919 : check 56 101 18 919 = true := by decide +kernel
theorem c920 : check 56 101 18 920 = true := by decide +kernel
theorem c921 : check 56 101 18 921 = true := by decide +kernel
theorem c922 : check 56 101 18 922 = true := by decide +kernel
theorem c923 : check 56 101 18 923 = true := by decide +kernel
theorem c924 : check 56 101 18 924 = true := by decide +kernel
theorem c925 : check 56 101 18 925 = true := by decide +kernel
theorem c926 : check 56 101 18 926 = true := by decide +kernel
theorem c927 : check 56 101 18 927 = true := by decide +kernel

theorem range : ChunksOK 56 101 18 912 16 :=
  (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c912) (chunksOK_one c913)) (chunksOK_append (chunksOK_one c914) (chunksOK_one c915))) (chunksOK_append (chunksOK_append (chunksOK_one c916) (chunksOK_one c917)) (chunksOK_append (chunksOK_one c918) (chunksOK_one c919)))) (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c920) (chunksOK_one c921)) (chunksOK_append (chunksOK_one c922) (chunksOK_one c923))) (chunksOK_append (chunksOK_append (chunksOK_one c924) (chunksOK_one c925)) (chunksOK_append (chunksOK_one c926) (chunksOK_one c927)))))

end KC.Q01W56.C57
