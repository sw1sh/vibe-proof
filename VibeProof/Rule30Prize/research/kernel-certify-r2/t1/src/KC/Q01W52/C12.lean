import KC.Q01Lanes

/-! Kernel checks for `Q01` at width `52`: chunks `192` to `207` of `256` (`2 ^ 18` lanes each, `97` levels). -/

namespace KC.Q01W52.C12
open KC.Q01Lanes

theorem c192 : check 52 97 18 192 = true := by decide +kernel
theorem c193 : check 52 97 18 193 = true := by decide +kernel
theorem c194 : check 52 97 18 194 = true := by decide +kernel
theorem c195 : check 52 97 18 195 = true := by decide +kernel
theorem c196 : check 52 97 18 196 = true := by decide +kernel
theorem c197 : check 52 97 18 197 = true := by decide +kernel
theorem c198 : check 52 97 18 198 = true := by decide +kernel
theorem c199 : check 52 97 18 199 = true := by decide +kernel
theorem c200 : check 52 97 18 200 = true := by decide +kernel
theorem c201 : check 52 97 18 201 = true := by decide +kernel
theorem c202 : check 52 97 18 202 = true := by decide +kernel
theorem c203 : check 52 97 18 203 = true := by decide +kernel
theorem c204 : check 52 97 18 204 = true := by decide +kernel
theorem c205 : check 52 97 18 205 = true := by decide +kernel
theorem c206 : check 52 97 18 206 = true := by decide +kernel
theorem c207 : check 52 97 18 207 = true := by decide +kernel

theorem range : ChunksOK 52 97 18 192 16 :=
  (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c192) (chunksOK_one c193)) (chunksOK_append (chunksOK_one c194) (chunksOK_one c195))) (chunksOK_append (chunksOK_append (chunksOK_one c196) (chunksOK_one c197)) (chunksOK_append (chunksOK_one c198) (chunksOK_one c199)))) (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c200) (chunksOK_one c201)) (chunksOK_append (chunksOK_one c202) (chunksOK_one c203))) (chunksOK_append (chunksOK_append (chunksOK_one c204) (chunksOK_one c205)) (chunksOK_append (chunksOK_one c206) (chunksOK_one c207)))))

end KC.Q01W52.C12
