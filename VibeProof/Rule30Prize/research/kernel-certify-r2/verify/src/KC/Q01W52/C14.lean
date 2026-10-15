import KC.Q01Lanes

/-! Kernel checks for `Q01` at width `52`: chunks `224` to `239` of `256` (`2 ^ 18` lanes each, `97` levels). -/

namespace KC.Q01W52.C14
open KC.Q01Lanes

theorem c224 : check 52 97 18 224 = true := by decide +kernel
theorem c225 : check 52 97 18 225 = true := by decide +kernel
theorem c226 : check 52 97 18 226 = true := by decide +kernel
theorem c227 : check 52 97 18 227 = true := by decide +kernel
theorem c228 : check 52 97 18 228 = true := by decide +kernel
theorem c229 : check 52 97 18 229 = true := by decide +kernel
theorem c230 : check 52 97 18 230 = true := by decide +kernel
theorem c231 : check 52 97 18 231 = true := by decide +kernel
theorem c232 : check 52 97 18 232 = true := by decide +kernel
theorem c233 : check 52 97 18 233 = true := by decide +kernel
theorem c234 : check 52 97 18 234 = true := by decide +kernel
theorem c235 : check 52 97 18 235 = true := by decide +kernel
theorem c236 : check 52 97 18 236 = true := by decide +kernel
theorem c237 : check 52 97 18 237 = true := by decide +kernel
theorem c238 : check 52 97 18 238 = true := by decide +kernel
theorem c239 : check 52 97 18 239 = true := by decide +kernel

theorem range : ChunksOK 52 97 18 224 16 :=
  (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c224) (chunksOK_one c225)) (chunksOK_append (chunksOK_one c226) (chunksOK_one c227))) (chunksOK_append (chunksOK_append (chunksOK_one c228) (chunksOK_one c229)) (chunksOK_append (chunksOK_one c230) (chunksOK_one c231)))) (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c232) (chunksOK_one c233)) (chunksOK_append (chunksOK_one c234) (chunksOK_one c235))) (chunksOK_append (chunksOK_append (chunksOK_one c236) (chunksOK_one c237)) (chunksOK_append (chunksOK_one c238) (chunksOK_one c239)))))

end KC.Q01W52.C14
