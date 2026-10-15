import KC.Q01Lanes

/-! Kernel checks for `Q01` at width `56`: chunks `384` to `399` of `1024` (`2 ^ 18` lanes each, `101` levels). -/

namespace KC.Q01W56.C24
open KC.Q01Lanes

theorem c384 : check 56 101 18 384 = true := by decide +kernel
theorem c385 : check 56 101 18 385 = true := by decide +kernel
theorem c386 : check 56 101 18 386 = true := by decide +kernel
theorem c387 : check 56 101 18 387 = true := by decide +kernel
theorem c388 : check 56 101 18 388 = true := by decide +kernel
theorem c389 : check 56 101 18 389 = true := by decide +kernel
theorem c390 : check 56 101 18 390 = true := by decide +kernel
theorem c391 : check 56 101 18 391 = true := by decide +kernel
theorem c392 : check 56 101 18 392 = true := by decide +kernel
theorem c393 : check 56 101 18 393 = true := by decide +kernel
theorem c394 : check 56 101 18 394 = true := by decide +kernel
theorem c395 : check 56 101 18 395 = true := by decide +kernel
theorem c396 : check 56 101 18 396 = true := by decide +kernel
theorem c397 : check 56 101 18 397 = true := by decide +kernel
theorem c398 : check 56 101 18 398 = true := by decide +kernel
theorem c399 : check 56 101 18 399 = true := by decide +kernel

theorem range : ChunksOK 56 101 18 384 16 :=
  (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c384) (chunksOK_one c385)) (chunksOK_append (chunksOK_one c386) (chunksOK_one c387))) (chunksOK_append (chunksOK_append (chunksOK_one c388) (chunksOK_one c389)) (chunksOK_append (chunksOK_one c390) (chunksOK_one c391)))) (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c392) (chunksOK_one c393)) (chunksOK_append (chunksOK_one c394) (chunksOK_one c395))) (chunksOK_append (chunksOK_append (chunksOK_one c396) (chunksOK_one c397)) (chunksOK_append (chunksOK_one c398) (chunksOK_one c399)))))

end KC.Q01W56.C24
