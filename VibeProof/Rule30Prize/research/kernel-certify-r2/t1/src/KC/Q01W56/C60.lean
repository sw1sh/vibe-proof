import KC.Q01Lanes

/-! Kernel checks for `Q01` at width `56`: chunks `960` to `975` of `1024` (`2 ^ 18` lanes each, `101` levels). -/

namespace KC.Q01W56.C60
open KC.Q01Lanes

theorem c960 : check 56 101 18 960 = true := by decide +kernel
theorem c961 : check 56 101 18 961 = true := by decide +kernel
theorem c962 : check 56 101 18 962 = true := by decide +kernel
theorem c963 : check 56 101 18 963 = true := by decide +kernel
theorem c964 : check 56 101 18 964 = true := by decide +kernel
theorem c965 : check 56 101 18 965 = true := by decide +kernel
theorem c966 : check 56 101 18 966 = true := by decide +kernel
theorem c967 : check 56 101 18 967 = true := by decide +kernel
theorem c968 : check 56 101 18 968 = true := by decide +kernel
theorem c969 : check 56 101 18 969 = true := by decide +kernel
theorem c970 : check 56 101 18 970 = true := by decide +kernel
theorem c971 : check 56 101 18 971 = true := by decide +kernel
theorem c972 : check 56 101 18 972 = true := by decide +kernel
theorem c973 : check 56 101 18 973 = true := by decide +kernel
theorem c974 : check 56 101 18 974 = true := by decide +kernel
theorem c975 : check 56 101 18 975 = true := by decide +kernel

theorem range : ChunksOK 56 101 18 960 16 :=
  (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c960) (chunksOK_one c961)) (chunksOK_append (chunksOK_one c962) (chunksOK_one c963))) (chunksOK_append (chunksOK_append (chunksOK_one c964) (chunksOK_one c965)) (chunksOK_append (chunksOK_one c966) (chunksOK_one c967)))) (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c968) (chunksOK_one c969)) (chunksOK_append (chunksOK_one c970) (chunksOK_one c971))) (chunksOK_append (chunksOK_append (chunksOK_one c972) (chunksOK_one c973)) (chunksOK_append (chunksOK_one c974) (chunksOK_one c975)))))

end KC.Q01W56.C60
