import KC.Q01Lanes

/-! Kernel checks for `Q01` at width `56`: chunks `400` to `415` of `1024` (`2 ^ 18` lanes each, `101` levels). -/

namespace KC.Q01W56.C25
open KC.Q01Lanes

theorem c400 : check 56 101 18 400 = true := by decide +kernel
theorem c401 : check 56 101 18 401 = true := by decide +kernel
theorem c402 : check 56 101 18 402 = true := by decide +kernel
theorem c403 : check 56 101 18 403 = true := by decide +kernel
theorem c404 : check 56 101 18 404 = true := by decide +kernel
theorem c405 : check 56 101 18 405 = true := by decide +kernel
theorem c406 : check 56 101 18 406 = true := by decide +kernel
theorem c407 : check 56 101 18 407 = true := by decide +kernel
theorem c408 : check 56 101 18 408 = true := by decide +kernel
theorem c409 : check 56 101 18 409 = true := by decide +kernel
theorem c410 : check 56 101 18 410 = true := by decide +kernel
theorem c411 : check 56 101 18 411 = true := by decide +kernel
theorem c412 : check 56 101 18 412 = true := by decide +kernel
theorem c413 : check 56 101 18 413 = true := by decide +kernel
theorem c414 : check 56 101 18 414 = true := by decide +kernel
theorem c415 : check 56 101 18 415 = true := by decide +kernel

theorem range : ChunksOK 56 101 18 400 16 :=
  (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c400) (chunksOK_one c401)) (chunksOK_append (chunksOK_one c402) (chunksOK_one c403))) (chunksOK_append (chunksOK_append (chunksOK_one c404) (chunksOK_one c405)) (chunksOK_append (chunksOK_one c406) (chunksOK_one c407)))) (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c408) (chunksOK_one c409)) (chunksOK_append (chunksOK_one c410) (chunksOK_one c411))) (chunksOK_append (chunksOK_append (chunksOK_one c412) (chunksOK_one c413)) (chunksOK_append (chunksOK_one c414) (chunksOK_one c415)))))

end KC.Q01W56.C25
