import KC.Q01Lanes

/-! Kernel checks for `Q01` at width `56`: chunks `32` to `47` of `1024` (`2 ^ 18` lanes each, `101` levels). -/

namespace KC.Q01W56.C2
open KC.Q01Lanes

theorem c32 : check 56 101 18 32 = true := by decide +kernel
theorem c33 : check 56 101 18 33 = true := by decide +kernel
theorem c34 : check 56 101 18 34 = true := by decide +kernel
theorem c35 : check 56 101 18 35 = true := by decide +kernel
theorem c36 : check 56 101 18 36 = true := by decide +kernel
theorem c37 : check 56 101 18 37 = true := by decide +kernel
theorem c38 : check 56 101 18 38 = true := by decide +kernel
theorem c39 : check 56 101 18 39 = true := by decide +kernel
theorem c40 : check 56 101 18 40 = true := by decide +kernel
theorem c41 : check 56 101 18 41 = true := by decide +kernel
theorem c42 : check 56 101 18 42 = true := by decide +kernel
theorem c43 : check 56 101 18 43 = true := by decide +kernel
theorem c44 : check 56 101 18 44 = true := by decide +kernel
theorem c45 : check 56 101 18 45 = true := by decide +kernel
theorem c46 : check 56 101 18 46 = true := by decide +kernel
theorem c47 : check 56 101 18 47 = true := by decide +kernel

theorem range : ChunksOK 56 101 18 32 16 :=
  (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c32) (chunksOK_one c33)) (chunksOK_append (chunksOK_one c34) (chunksOK_one c35))) (chunksOK_append (chunksOK_append (chunksOK_one c36) (chunksOK_one c37)) (chunksOK_append (chunksOK_one c38) (chunksOK_one c39)))) (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c40) (chunksOK_one c41)) (chunksOK_append (chunksOK_one c42) (chunksOK_one c43))) (chunksOK_append (chunksOK_append (chunksOK_one c44) (chunksOK_one c45)) (chunksOK_append (chunksOK_one c46) (chunksOK_one c47)))))

end KC.Q01W56.C2
