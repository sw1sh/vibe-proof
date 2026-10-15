import KC.Q01Lanes

/-! Kernel checks for `Q01` at width `56`: chunks `896` to `911` of `1024` (`2 ^ 18` lanes each, `101` levels). -/

namespace KC.Q01W56.C56
open KC.Q01Lanes

theorem c896 : check 56 101 18 896 = true := by decide +kernel
theorem c897 : check 56 101 18 897 = true := by decide +kernel
theorem c898 : check 56 101 18 898 = true := by decide +kernel
theorem c899 : check 56 101 18 899 = true := by decide +kernel
theorem c900 : check 56 101 18 900 = true := by decide +kernel
theorem c901 : check 56 101 18 901 = true := by decide +kernel
theorem c902 : check 56 101 18 902 = true := by decide +kernel
theorem c903 : check 56 101 18 903 = true := by decide +kernel
theorem c904 : check 56 101 18 904 = true := by decide +kernel
theorem c905 : check 56 101 18 905 = true := by decide +kernel
theorem c906 : check 56 101 18 906 = true := by decide +kernel
theorem c907 : check 56 101 18 907 = true := by decide +kernel
theorem c908 : check 56 101 18 908 = true := by decide +kernel
theorem c909 : check 56 101 18 909 = true := by decide +kernel
theorem c910 : check 56 101 18 910 = true := by decide +kernel
theorem c911 : check 56 101 18 911 = true := by decide +kernel

theorem range : ChunksOK 56 101 18 896 16 :=
  (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c896) (chunksOK_one c897)) (chunksOK_append (chunksOK_one c898) (chunksOK_one c899))) (chunksOK_append (chunksOK_append (chunksOK_one c900) (chunksOK_one c901)) (chunksOK_append (chunksOK_one c902) (chunksOK_one c903)))) (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c904) (chunksOK_one c905)) (chunksOK_append (chunksOK_one c906) (chunksOK_one c907))) (chunksOK_append (chunksOK_append (chunksOK_one c908) (chunksOK_one c909)) (chunksOK_append (chunksOK_one c910) (chunksOK_one c911)))))

end KC.Q01W56.C56
