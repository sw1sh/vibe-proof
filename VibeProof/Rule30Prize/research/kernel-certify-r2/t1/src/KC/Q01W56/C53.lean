import KC.Q01Lanes

/-! Kernel checks for `Q01` at width `56`: chunks `848` to `863` of `1024` (`2 ^ 18` lanes each, `101` levels). -/

namespace KC.Q01W56.C53
open KC.Q01Lanes

theorem c848 : check 56 101 18 848 = true := by decide +kernel
theorem c849 : check 56 101 18 849 = true := by decide +kernel
theorem c850 : check 56 101 18 850 = true := by decide +kernel
theorem c851 : check 56 101 18 851 = true := by decide +kernel
theorem c852 : check 56 101 18 852 = true := by decide +kernel
theorem c853 : check 56 101 18 853 = true := by decide +kernel
theorem c854 : check 56 101 18 854 = true := by decide +kernel
theorem c855 : check 56 101 18 855 = true := by decide +kernel
theorem c856 : check 56 101 18 856 = true := by decide +kernel
theorem c857 : check 56 101 18 857 = true := by decide +kernel
theorem c858 : check 56 101 18 858 = true := by decide +kernel
theorem c859 : check 56 101 18 859 = true := by decide +kernel
theorem c860 : check 56 101 18 860 = true := by decide +kernel
theorem c861 : check 56 101 18 861 = true := by decide +kernel
theorem c862 : check 56 101 18 862 = true := by decide +kernel
theorem c863 : check 56 101 18 863 = true := by decide +kernel

theorem range : ChunksOK 56 101 18 848 16 :=
  (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c848) (chunksOK_one c849)) (chunksOK_append (chunksOK_one c850) (chunksOK_one c851))) (chunksOK_append (chunksOK_append (chunksOK_one c852) (chunksOK_one c853)) (chunksOK_append (chunksOK_one c854) (chunksOK_one c855)))) (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c856) (chunksOK_one c857)) (chunksOK_append (chunksOK_one c858) (chunksOK_one c859))) (chunksOK_append (chunksOK_append (chunksOK_one c860) (chunksOK_one c861)) (chunksOK_append (chunksOK_one c862) (chunksOK_one c863)))))

end KC.Q01W56.C53
