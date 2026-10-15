import KC.Q01Lanes

/-! Kernel checks for `Q01` at width `52`: chunks `240` to `255` of `256` (`2 ^ 18` lanes each, `97` levels). -/

namespace KC.Q01W52.C15
open KC.Q01Lanes

theorem c240 : check 52 97 18 240 = true := by decide +kernel
theorem c241 : check 52 97 18 241 = true := by decide +kernel
theorem c242 : check 52 97 18 242 = true := by decide +kernel
theorem c243 : check 52 97 18 243 = true := by decide +kernel
theorem c244 : check 52 97 18 244 = true := by decide +kernel
theorem c245 : check 52 97 18 245 = true := by decide +kernel
theorem c246 : check 52 97 18 246 = true := by decide +kernel
theorem c247 : check 52 97 18 247 = true := by decide +kernel
theorem c248 : check 52 97 18 248 = true := by decide +kernel
theorem c249 : check 52 97 18 249 = true := by decide +kernel
theorem c250 : check 52 97 18 250 = true := by decide +kernel
theorem c251 : check 52 97 18 251 = true := by decide +kernel
theorem c252 : check 52 97 18 252 = true := by decide +kernel
theorem c253 : check 52 97 18 253 = true := by decide +kernel
theorem c254 : check 52 97 18 254 = true := by decide +kernel
theorem c255 : check 52 97 18 255 = true := by decide +kernel

theorem range : ChunksOK 52 97 18 240 16 :=
  (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c240) (chunksOK_one c241)) (chunksOK_append (chunksOK_one c242) (chunksOK_one c243))) (chunksOK_append (chunksOK_append (chunksOK_one c244) (chunksOK_one c245)) (chunksOK_append (chunksOK_one c246) (chunksOK_one c247)))) (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c248) (chunksOK_one c249)) (chunksOK_append (chunksOK_one c250) (chunksOK_one c251))) (chunksOK_append (chunksOK_append (chunksOK_one c252) (chunksOK_one c253)) (chunksOK_append (chunksOK_one c254) (chunksOK_one c255)))))

end KC.Q01W52.C15
