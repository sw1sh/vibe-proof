import KC.Q01Lanes

/-! Kernel checks for `Q01` at width `56`: chunks `432` to `447` of `1024` (`2 ^ 18` lanes each, `101` levels). -/

namespace KC.Q01W56.C27
open KC.Q01Lanes

theorem c432 : check 56 101 18 432 = true := by decide +kernel
theorem c433 : check 56 101 18 433 = true := by decide +kernel
theorem c434 : check 56 101 18 434 = true := by decide +kernel
theorem c435 : check 56 101 18 435 = true := by decide +kernel
theorem c436 : check 56 101 18 436 = true := by decide +kernel
theorem c437 : check 56 101 18 437 = true := by decide +kernel
theorem c438 : check 56 101 18 438 = true := by decide +kernel
theorem c439 : check 56 101 18 439 = true := by decide +kernel
theorem c440 : check 56 101 18 440 = true := by decide +kernel
theorem c441 : check 56 101 18 441 = true := by decide +kernel
theorem c442 : check 56 101 18 442 = true := by decide +kernel
theorem c443 : check 56 101 18 443 = true := by decide +kernel
theorem c444 : check 56 101 18 444 = true := by decide +kernel
theorem c445 : check 56 101 18 445 = true := by decide +kernel
theorem c446 : check 56 101 18 446 = true := by decide +kernel
theorem c447 : check 56 101 18 447 = true := by decide +kernel

theorem range : ChunksOK 56 101 18 432 16 :=
  (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c432) (chunksOK_one c433)) (chunksOK_append (chunksOK_one c434) (chunksOK_one c435))) (chunksOK_append (chunksOK_append (chunksOK_one c436) (chunksOK_one c437)) (chunksOK_append (chunksOK_one c438) (chunksOK_one c439)))) (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c440) (chunksOK_one c441)) (chunksOK_append (chunksOK_one c442) (chunksOK_one c443))) (chunksOK_append (chunksOK_append (chunksOK_one c444) (chunksOK_one c445)) (chunksOK_append (chunksOK_one c446) (chunksOK_one c447)))))

end KC.Q01W56.C27
