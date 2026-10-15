import KC.Q01Lanes

/-! Kernel checks for `Q01` at width `56`: chunks `816` to `831` of `1024` (`2 ^ 18` lanes each, `101` levels). -/

namespace KC.Q01W56.C51
open KC.Q01Lanes

theorem c816 : check 56 101 18 816 = true := by decide +kernel
theorem c817 : check 56 101 18 817 = true := by decide +kernel
theorem c818 : check 56 101 18 818 = true := by decide +kernel
theorem c819 : check 56 101 18 819 = true := by decide +kernel
theorem c820 : check 56 101 18 820 = true := by decide +kernel
theorem c821 : check 56 101 18 821 = true := by decide +kernel
theorem c822 : check 56 101 18 822 = true := by decide +kernel
theorem c823 : check 56 101 18 823 = true := by decide +kernel
theorem c824 : check 56 101 18 824 = true := by decide +kernel
theorem c825 : check 56 101 18 825 = true := by decide +kernel
theorem c826 : check 56 101 18 826 = true := by decide +kernel
theorem c827 : check 56 101 18 827 = true := by decide +kernel
theorem c828 : check 56 101 18 828 = true := by decide +kernel
theorem c829 : check 56 101 18 829 = true := by decide +kernel
theorem c830 : check 56 101 18 830 = true := by decide +kernel
theorem c831 : check 56 101 18 831 = true := by decide +kernel

theorem range : ChunksOK 56 101 18 816 16 :=
  (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c816) (chunksOK_one c817)) (chunksOK_append (chunksOK_one c818) (chunksOK_one c819))) (chunksOK_append (chunksOK_append (chunksOK_one c820) (chunksOK_one c821)) (chunksOK_append (chunksOK_one c822) (chunksOK_one c823)))) (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c824) (chunksOK_one c825)) (chunksOK_append (chunksOK_one c826) (chunksOK_one c827))) (chunksOK_append (chunksOK_append (chunksOK_one c828) (chunksOK_one c829)) (chunksOK_append (chunksOK_one c830) (chunksOK_one c831)))))

end KC.Q01W56.C51
