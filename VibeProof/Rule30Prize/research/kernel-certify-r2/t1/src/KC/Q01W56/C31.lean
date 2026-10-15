import KC.Q01Lanes

/-! Kernel checks for `Q01` at width `56`: chunks `496` to `511` of `1024` (`2 ^ 18` lanes each, `101` levels). -/

namespace KC.Q01W56.C31
open KC.Q01Lanes

theorem c496 : check 56 101 18 496 = true := by decide +kernel
theorem c497 : check 56 101 18 497 = true := by decide +kernel
theorem c498 : check 56 101 18 498 = true := by decide +kernel
theorem c499 : check 56 101 18 499 = true := by decide +kernel
theorem c500 : check 56 101 18 500 = true := by decide +kernel
theorem c501 : check 56 101 18 501 = true := by decide +kernel
theorem c502 : check 56 101 18 502 = true := by decide +kernel
theorem c503 : check 56 101 18 503 = true := by decide +kernel
theorem c504 : check 56 101 18 504 = true := by decide +kernel
theorem c505 : check 56 101 18 505 = true := by decide +kernel
theorem c506 : check 56 101 18 506 = true := by decide +kernel
theorem c507 : check 56 101 18 507 = true := by decide +kernel
theorem c508 : check 56 101 18 508 = true := by decide +kernel
theorem c509 : check 56 101 18 509 = true := by decide +kernel
theorem c510 : check 56 101 18 510 = true := by decide +kernel
theorem c511 : check 56 101 18 511 = true := by decide +kernel

theorem range : ChunksOK 56 101 18 496 16 :=
  (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c496) (chunksOK_one c497)) (chunksOK_append (chunksOK_one c498) (chunksOK_one c499))) (chunksOK_append (chunksOK_append (chunksOK_one c500) (chunksOK_one c501)) (chunksOK_append (chunksOK_one c502) (chunksOK_one c503)))) (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c504) (chunksOK_one c505)) (chunksOK_append (chunksOK_one c506) (chunksOK_one c507))) (chunksOK_append (chunksOK_append (chunksOK_one c508) (chunksOK_one c509)) (chunksOK_append (chunksOK_one c510) (chunksOK_one c511)))))

end KC.Q01W56.C31
