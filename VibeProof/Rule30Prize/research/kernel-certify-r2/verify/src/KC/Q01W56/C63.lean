import KC.Q01Lanes

/-! Kernel checks for `Q01` at width `56`: chunks `1008` to `1023` of `1024` (`2 ^ 18` lanes each, `101` levels). -/

namespace KC.Q01W56.C63
open KC.Q01Lanes

theorem c1008 : check 56 101 18 1008 = true := by decide +kernel
theorem c1009 : check 56 101 18 1009 = true := by decide +kernel
theorem c1010 : check 56 101 18 1010 = true := by decide +kernel
theorem c1011 : check 56 101 18 1011 = true := by decide +kernel
theorem c1012 : check 56 101 18 1012 = true := by decide +kernel
theorem c1013 : check 56 101 18 1013 = true := by decide +kernel
theorem c1014 : check 56 101 18 1014 = true := by decide +kernel
theorem c1015 : check 56 101 18 1015 = true := by decide +kernel
theorem c1016 : check 56 101 18 1016 = true := by decide +kernel
theorem c1017 : check 56 101 18 1017 = true := by decide +kernel
theorem c1018 : check 56 101 18 1018 = true := by decide +kernel
theorem c1019 : check 56 101 18 1019 = true := by decide +kernel
theorem c1020 : check 56 101 18 1020 = true := by decide +kernel
theorem c1021 : check 56 101 18 1021 = true := by decide +kernel
theorem c1022 : check 56 101 18 1022 = true := by decide +kernel
theorem c1023 : check 56 101 18 1023 = true := by decide +kernel

theorem range : ChunksOK 56 101 18 1008 16 :=
  (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c1008) (chunksOK_one c1009)) (chunksOK_append (chunksOK_one c1010) (chunksOK_one c1011))) (chunksOK_append (chunksOK_append (chunksOK_one c1012) (chunksOK_one c1013)) (chunksOK_append (chunksOK_one c1014) (chunksOK_one c1015)))) (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c1016) (chunksOK_one c1017)) (chunksOK_append (chunksOK_one c1018) (chunksOK_one c1019))) (chunksOK_append (chunksOK_append (chunksOK_one c1020) (chunksOK_one c1021)) (chunksOK_append (chunksOK_one c1022) (chunksOK_one c1023)))))

end KC.Q01W56.C63
