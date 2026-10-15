import KC.Q01Lanes

/-! Kernel checks for `Q01` at width `56`: chunks `576` to `591` of `1024` (`2 ^ 18` lanes each, `101` levels). -/

namespace KC.Q01W56.C36
open KC.Q01Lanes

theorem c576 : check 56 101 18 576 = true := by decide +kernel
theorem c577 : check 56 101 18 577 = true := by decide +kernel
theorem c578 : check 56 101 18 578 = true := by decide +kernel
theorem c579 : check 56 101 18 579 = true := by decide +kernel
theorem c580 : check 56 101 18 580 = true := by decide +kernel
theorem c581 : check 56 101 18 581 = true := by decide +kernel
theorem c582 : check 56 101 18 582 = true := by decide +kernel
theorem c583 : check 56 101 18 583 = true := by decide +kernel
theorem c584 : check 56 101 18 584 = true := by decide +kernel
theorem c585 : check 56 101 18 585 = true := by decide +kernel
theorem c586 : check 56 101 18 586 = true := by decide +kernel
theorem c587 : check 56 101 18 587 = true := by decide +kernel
theorem c588 : check 56 101 18 588 = true := by decide +kernel
theorem c589 : check 56 101 18 589 = true := by decide +kernel
theorem c590 : check 56 101 18 590 = true := by decide +kernel
theorem c591 : check 56 101 18 591 = true := by decide +kernel

theorem range : ChunksOK 56 101 18 576 16 :=
  (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c576) (chunksOK_one c577)) (chunksOK_append (chunksOK_one c578) (chunksOK_one c579))) (chunksOK_append (chunksOK_append (chunksOK_one c580) (chunksOK_one c581)) (chunksOK_append (chunksOK_one c582) (chunksOK_one c583)))) (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c584) (chunksOK_one c585)) (chunksOK_append (chunksOK_one c586) (chunksOK_one c587))) (chunksOK_append (chunksOK_append (chunksOK_one c588) (chunksOK_one c589)) (chunksOK_append (chunksOK_one c590) (chunksOK_one c591)))))

end KC.Q01W56.C36
