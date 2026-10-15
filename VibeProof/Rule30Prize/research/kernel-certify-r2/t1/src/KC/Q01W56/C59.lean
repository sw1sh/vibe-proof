import KC.Q01Lanes

/-! Kernel checks for `Q01` at width `56`: chunks `944` to `959` of `1024` (`2 ^ 18` lanes each, `101` levels). -/

namespace KC.Q01W56.C59
open KC.Q01Lanes

theorem c944 : check 56 101 18 944 = true := by decide +kernel
theorem c945 : check 56 101 18 945 = true := by decide +kernel
theorem c946 : check 56 101 18 946 = true := by decide +kernel
theorem c947 : check 56 101 18 947 = true := by decide +kernel
theorem c948 : check 56 101 18 948 = true := by decide +kernel
theorem c949 : check 56 101 18 949 = true := by decide +kernel
theorem c950 : check 56 101 18 950 = true := by decide +kernel
theorem c951 : check 56 101 18 951 = true := by decide +kernel
theorem c952 : check 56 101 18 952 = true := by decide +kernel
theorem c953 : check 56 101 18 953 = true := by decide +kernel
theorem c954 : check 56 101 18 954 = true := by decide +kernel
theorem c955 : check 56 101 18 955 = true := by decide +kernel
theorem c956 : check 56 101 18 956 = true := by decide +kernel
theorem c957 : check 56 101 18 957 = true := by decide +kernel
theorem c958 : check 56 101 18 958 = true := by decide +kernel
theorem c959 : check 56 101 18 959 = true := by decide +kernel

theorem range : ChunksOK 56 101 18 944 16 :=
  (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c944) (chunksOK_one c945)) (chunksOK_append (chunksOK_one c946) (chunksOK_one c947))) (chunksOK_append (chunksOK_append (chunksOK_one c948) (chunksOK_one c949)) (chunksOK_append (chunksOK_one c950) (chunksOK_one c951)))) (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c952) (chunksOK_one c953)) (chunksOK_append (chunksOK_one c954) (chunksOK_one c955))) (chunksOK_append (chunksOK_append (chunksOK_one c956) (chunksOK_one c957)) (chunksOK_append (chunksOK_one c958) (chunksOK_one c959)))))

end KC.Q01W56.C59
