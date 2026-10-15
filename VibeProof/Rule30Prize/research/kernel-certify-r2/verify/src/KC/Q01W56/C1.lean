import KC.Q01Lanes

/-! Kernel checks for `Q01` at width `56`: chunks `16` to `31` of `1024` (`2 ^ 18` lanes each, `101` levels). -/

namespace KC.Q01W56.C1
open KC.Q01Lanes

theorem c16 : check 56 101 18 16 = true := by decide +kernel
theorem c17 : check 56 101 18 17 = true := by decide +kernel
theorem c18 : check 56 101 18 18 = true := by decide +kernel
theorem c19 : check 56 101 18 19 = true := by decide +kernel
theorem c20 : check 56 101 18 20 = true := by decide +kernel
theorem c21 : check 56 101 18 21 = true := by decide +kernel
theorem c22 : check 56 101 18 22 = true := by decide +kernel
theorem c23 : check 56 101 18 23 = true := by decide +kernel
theorem c24 : check 56 101 18 24 = true := by decide +kernel
theorem c25 : check 56 101 18 25 = true := by decide +kernel
theorem c26 : check 56 101 18 26 = true := by decide +kernel
theorem c27 : check 56 101 18 27 = true := by decide +kernel
theorem c28 : check 56 101 18 28 = true := by decide +kernel
theorem c29 : check 56 101 18 29 = true := by decide +kernel
theorem c30 : check 56 101 18 30 = true := by decide +kernel
theorem c31 : check 56 101 18 31 = true := by decide +kernel

theorem range : ChunksOK 56 101 18 16 16 :=
  (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c16) (chunksOK_one c17)) (chunksOK_append (chunksOK_one c18) (chunksOK_one c19))) (chunksOK_append (chunksOK_append (chunksOK_one c20) (chunksOK_one c21)) (chunksOK_append (chunksOK_one c22) (chunksOK_one c23)))) (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c24) (chunksOK_one c25)) (chunksOK_append (chunksOK_one c26) (chunksOK_one c27))) (chunksOK_append (chunksOK_append (chunksOK_one c28) (chunksOK_one c29)) (chunksOK_append (chunksOK_one c30) (chunksOK_one c31)))))

end KC.Q01W56.C1
