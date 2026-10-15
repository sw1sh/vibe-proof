import KC.Q01Lanes

/-! Kernel checks for `Q01` at width `52`: chunks `48` to `63` of `256` (`2 ^ 18` lanes each, `97` levels). -/

namespace KC.Q01W52.C3
open KC.Q01Lanes

theorem c48 : check 52 97 18 48 = true := by decide +kernel
theorem c49 : check 52 97 18 49 = true := by decide +kernel
theorem c50 : check 52 97 18 50 = true := by decide +kernel
theorem c51 : check 52 97 18 51 = true := by decide +kernel
theorem c52 : check 52 97 18 52 = true := by decide +kernel
theorem c53 : check 52 97 18 53 = true := by decide +kernel
theorem c54 : check 52 97 18 54 = true := by decide +kernel
theorem c55 : check 52 97 18 55 = true := by decide +kernel
theorem c56 : check 52 97 18 56 = true := by decide +kernel
theorem c57 : check 52 97 18 57 = true := by decide +kernel
theorem c58 : check 52 97 18 58 = true := by decide +kernel
theorem c59 : check 52 97 18 59 = true := by decide +kernel
theorem c60 : check 52 97 18 60 = true := by decide +kernel
theorem c61 : check 52 97 18 61 = true := by decide +kernel
theorem c62 : check 52 97 18 62 = true := by decide +kernel
theorem c63 : check 52 97 18 63 = true := by decide +kernel

theorem range : ChunksOK 52 97 18 48 16 :=
  (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c48) (chunksOK_one c49)) (chunksOK_append (chunksOK_one c50) (chunksOK_one c51))) (chunksOK_append (chunksOK_append (chunksOK_one c52) (chunksOK_one c53)) (chunksOK_append (chunksOK_one c54) (chunksOK_one c55)))) (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c56) (chunksOK_one c57)) (chunksOK_append (chunksOK_one c58) (chunksOK_one c59))) (chunksOK_append (chunksOK_append (chunksOK_one c60) (chunksOK_one c61)) (chunksOK_append (chunksOK_one c62) (chunksOK_one c63)))))

end KC.Q01W52.C3
