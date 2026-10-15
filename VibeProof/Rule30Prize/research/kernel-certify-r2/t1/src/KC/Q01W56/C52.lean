import KC.Q01Lanes

/-! Kernel checks for `Q01` at width `56`: chunks `832` to `847` of `1024` (`2 ^ 18` lanes each, `101` levels). -/

namespace KC.Q01W56.C52
open KC.Q01Lanes

theorem c832 : check 56 101 18 832 = true := by decide +kernel
theorem c833 : check 56 101 18 833 = true := by decide +kernel
theorem c834 : check 56 101 18 834 = true := by decide +kernel
theorem c835 : check 56 101 18 835 = true := by decide +kernel
theorem c836 : check 56 101 18 836 = true := by decide +kernel
theorem c837 : check 56 101 18 837 = true := by decide +kernel
theorem c838 : check 56 101 18 838 = true := by decide +kernel
theorem c839 : check 56 101 18 839 = true := by decide +kernel
theorem c840 : check 56 101 18 840 = true := by decide +kernel
theorem c841 : check 56 101 18 841 = true := by decide +kernel
theorem c842 : check 56 101 18 842 = true := by decide +kernel
theorem c843 : check 56 101 18 843 = true := by decide +kernel
theorem c844 : check 56 101 18 844 = true := by decide +kernel
theorem c845 : check 56 101 18 845 = true := by decide +kernel
theorem c846 : check 56 101 18 846 = true := by decide +kernel
theorem c847 : check 56 101 18 847 = true := by decide +kernel

theorem range : ChunksOK 56 101 18 832 16 :=
  (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c832) (chunksOK_one c833)) (chunksOK_append (chunksOK_one c834) (chunksOK_one c835))) (chunksOK_append (chunksOK_append (chunksOK_one c836) (chunksOK_one c837)) (chunksOK_append (chunksOK_one c838) (chunksOK_one c839)))) (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c840) (chunksOK_one c841)) (chunksOK_append (chunksOK_one c842) (chunksOK_one c843))) (chunksOK_append (chunksOK_append (chunksOK_one c844) (chunksOK_one c845)) (chunksOK_append (chunksOK_one c846) (chunksOK_one c847)))))

end KC.Q01W56.C52
