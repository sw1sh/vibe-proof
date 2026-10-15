import KC.Q01Lanes

/-! Kernel checks for `Q01` at width `52`: chunks `0` to `15` of `256` (`2 ^ 18` lanes each, `97` levels). -/

namespace KC.Q01W52.C0
open KC.Q01Lanes

theorem c0 : check 52 97 18 0 = true := by decide +kernel
theorem c1 : check 52 97 18 1 = true := by decide +kernel
theorem c2 : check 52 97 18 2 = true := by decide +kernel
theorem c3 : check 52 97 18 3 = true := by decide +kernel
theorem c4 : check 52 97 18 4 = true := by decide +kernel
theorem c5 : check 52 97 18 5 = true := by decide +kernel
theorem c6 : check 52 97 18 6 = true := by decide +kernel
theorem c7 : check 52 97 18 7 = true := by decide +kernel
theorem c8 : check 52 97 18 8 = true := by decide +kernel
theorem c9 : check 52 97 18 9 = true := by decide +kernel
theorem c10 : check 52 97 18 10 = true := by decide +kernel
theorem c11 : check 52 97 18 11 = true := by decide +kernel
theorem c12 : check 52 97 18 12 = true := by decide +kernel
theorem c13 : check 52 97 18 13 = true := by decide +kernel
theorem c14 : check 52 97 18 14 = true := by decide +kernel
theorem c15 : check 52 97 18 15 = true := by decide +kernel

theorem range : ChunksOK 52 97 18 0 16 :=
  (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c0) (chunksOK_one c1)) (chunksOK_append (chunksOK_one c2) (chunksOK_one c3))) (chunksOK_append (chunksOK_append (chunksOK_one c4) (chunksOK_one c5)) (chunksOK_append (chunksOK_one c6) (chunksOK_one c7)))) (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c8) (chunksOK_one c9)) (chunksOK_append (chunksOK_one c10) (chunksOK_one c11))) (chunksOK_append (chunksOK_append (chunksOK_one c12) (chunksOK_one c13)) (chunksOK_append (chunksOK_one c14) (chunksOK_one c15)))))

end KC.Q01W52.C0
