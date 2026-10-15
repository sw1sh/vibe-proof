import KC.Q01Lanes

/-! Kernel checks for `Q01` at width `56`: chunks `624` to `639` of `1024` (`2 ^ 18` lanes each, `101` levels). -/

namespace KC.Q01W56.C39
open KC.Q01Lanes

theorem c624 : check 56 101 18 624 = true := by decide +kernel
theorem c625 : check 56 101 18 625 = true := by decide +kernel
theorem c626 : check 56 101 18 626 = true := by decide +kernel
theorem c627 : check 56 101 18 627 = true := by decide +kernel
theorem c628 : check 56 101 18 628 = true := by decide +kernel
theorem c629 : check 56 101 18 629 = true := by decide +kernel
theorem c630 : check 56 101 18 630 = true := by decide +kernel
theorem c631 : check 56 101 18 631 = true := by decide +kernel
theorem c632 : check 56 101 18 632 = true := by decide +kernel
theorem c633 : check 56 101 18 633 = true := by decide +kernel
theorem c634 : check 56 101 18 634 = true := by decide +kernel
theorem c635 : check 56 101 18 635 = true := by decide +kernel
theorem c636 : check 56 101 18 636 = true := by decide +kernel
theorem c637 : check 56 101 18 637 = true := by decide +kernel
theorem c638 : check 56 101 18 638 = true := by decide +kernel
theorem c639 : check 56 101 18 639 = true := by decide +kernel

theorem range : ChunksOK 56 101 18 624 16 :=
  (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c624) (chunksOK_one c625)) (chunksOK_append (chunksOK_one c626) (chunksOK_one c627))) (chunksOK_append (chunksOK_append (chunksOK_one c628) (chunksOK_one c629)) (chunksOK_append (chunksOK_one c630) (chunksOK_one c631)))) (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c632) (chunksOK_one c633)) (chunksOK_append (chunksOK_one c634) (chunksOK_one c635))) (chunksOK_append (chunksOK_append (chunksOK_one c636) (chunksOK_one c637)) (chunksOK_append (chunksOK_one c638) (chunksOK_one c639)))))

end KC.Q01W56.C39
