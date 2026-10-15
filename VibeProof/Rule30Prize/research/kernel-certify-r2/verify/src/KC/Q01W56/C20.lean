import KC.Q01Lanes

/-! Kernel checks for `Q01` at width `56`: chunks `320` to `335` of `1024` (`2 ^ 18` lanes each, `101` levels). -/

namespace KC.Q01W56.C20
open KC.Q01Lanes

theorem c320 : check 56 101 18 320 = true := by decide +kernel
theorem c321 : check 56 101 18 321 = true := by decide +kernel
theorem c322 : check 56 101 18 322 = true := by decide +kernel
theorem c323 : check 56 101 18 323 = true := by decide +kernel
theorem c324 : check 56 101 18 324 = true := by decide +kernel
theorem c325 : check 56 101 18 325 = true := by decide +kernel
theorem c326 : check 56 101 18 326 = true := by decide +kernel
theorem c327 : check 56 101 18 327 = true := by decide +kernel
theorem c328 : check 56 101 18 328 = true := by decide +kernel
theorem c329 : check 56 101 18 329 = true := by decide +kernel
theorem c330 : check 56 101 18 330 = true := by decide +kernel
theorem c331 : check 56 101 18 331 = true := by decide +kernel
theorem c332 : check 56 101 18 332 = true := by decide +kernel
theorem c333 : check 56 101 18 333 = true := by decide +kernel
theorem c334 : check 56 101 18 334 = true := by decide +kernel
theorem c335 : check 56 101 18 335 = true := by decide +kernel

theorem range : ChunksOK 56 101 18 320 16 :=
  (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c320) (chunksOK_one c321)) (chunksOK_append (chunksOK_one c322) (chunksOK_one c323))) (chunksOK_append (chunksOK_append (chunksOK_one c324) (chunksOK_one c325)) (chunksOK_append (chunksOK_one c326) (chunksOK_one c327)))) (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c328) (chunksOK_one c329)) (chunksOK_append (chunksOK_one c330) (chunksOK_one c331))) (chunksOK_append (chunksOK_append (chunksOK_one c332) (chunksOK_one c333)) (chunksOK_append (chunksOK_one c334) (chunksOK_one c335)))))

end KC.Q01W56.C20
