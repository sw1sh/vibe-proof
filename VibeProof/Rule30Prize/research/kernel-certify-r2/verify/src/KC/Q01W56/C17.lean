import KC.Q01Lanes

/-! Kernel checks for `Q01` at width `56`: chunks `272` to `287` of `1024` (`2 ^ 18` lanes each, `101` levels). -/

namespace KC.Q01W56.C17
open KC.Q01Lanes

theorem c272 : check 56 101 18 272 = true := by decide +kernel
theorem c273 : check 56 101 18 273 = true := by decide +kernel
theorem c274 : check 56 101 18 274 = true := by decide +kernel
theorem c275 : check 56 101 18 275 = true := by decide +kernel
theorem c276 : check 56 101 18 276 = true := by decide +kernel
theorem c277 : check 56 101 18 277 = true := by decide +kernel
theorem c278 : check 56 101 18 278 = true := by decide +kernel
theorem c279 : check 56 101 18 279 = true := by decide +kernel
theorem c280 : check 56 101 18 280 = true := by decide +kernel
theorem c281 : check 56 101 18 281 = true := by decide +kernel
theorem c282 : check 56 101 18 282 = true := by decide +kernel
theorem c283 : check 56 101 18 283 = true := by decide +kernel
theorem c284 : check 56 101 18 284 = true := by decide +kernel
theorem c285 : check 56 101 18 285 = true := by decide +kernel
theorem c286 : check 56 101 18 286 = true := by decide +kernel
theorem c287 : check 56 101 18 287 = true := by decide +kernel

theorem range : ChunksOK 56 101 18 272 16 :=
  (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c272) (chunksOK_one c273)) (chunksOK_append (chunksOK_one c274) (chunksOK_one c275))) (chunksOK_append (chunksOK_append (chunksOK_one c276) (chunksOK_one c277)) (chunksOK_append (chunksOK_one c278) (chunksOK_one c279)))) (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c280) (chunksOK_one c281)) (chunksOK_append (chunksOK_one c282) (chunksOK_one c283))) (chunksOK_append (chunksOK_append (chunksOK_one c284) (chunksOK_one c285)) (chunksOK_append (chunksOK_one c286) (chunksOK_one c287)))))

end KC.Q01W56.C17
