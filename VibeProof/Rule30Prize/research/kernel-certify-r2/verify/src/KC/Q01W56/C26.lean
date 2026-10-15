import KC.Q01Lanes

/-! Kernel checks for `Q01` at width `56`: chunks `416` to `431` of `1024` (`2 ^ 18` lanes each, `101` levels). -/

namespace KC.Q01W56.C26
open KC.Q01Lanes

theorem c416 : check 56 101 18 416 = true := by decide +kernel
theorem c417 : check 56 101 18 417 = true := by decide +kernel
theorem c418 : check 56 101 18 418 = true := by decide +kernel
theorem c419 : check 56 101 18 419 = true := by decide +kernel
theorem c420 : check 56 101 18 420 = true := by decide +kernel
theorem c421 : check 56 101 18 421 = true := by decide +kernel
theorem c422 : check 56 101 18 422 = true := by decide +kernel
theorem c423 : check 56 101 18 423 = true := by decide +kernel
theorem c424 : check 56 101 18 424 = true := by decide +kernel
theorem c425 : check 56 101 18 425 = true := by decide +kernel
theorem c426 : check 56 101 18 426 = true := by decide +kernel
theorem c427 : check 56 101 18 427 = true := by decide +kernel
theorem c428 : check 56 101 18 428 = true := by decide +kernel
theorem c429 : check 56 101 18 429 = true := by decide +kernel
theorem c430 : check 56 101 18 430 = true := by decide +kernel
theorem c431 : check 56 101 18 431 = true := by decide +kernel

theorem range : ChunksOK 56 101 18 416 16 :=
  (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c416) (chunksOK_one c417)) (chunksOK_append (chunksOK_one c418) (chunksOK_one c419))) (chunksOK_append (chunksOK_append (chunksOK_one c420) (chunksOK_one c421)) (chunksOK_append (chunksOK_one c422) (chunksOK_one c423)))) (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c424) (chunksOK_one c425)) (chunksOK_append (chunksOK_one c426) (chunksOK_one c427))) (chunksOK_append (chunksOK_append (chunksOK_one c428) (chunksOK_one c429)) (chunksOK_append (chunksOK_one c430) (chunksOK_one c431)))))

end KC.Q01W56.C26
