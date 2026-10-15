import KC.Q01Lanes

/-! Kernel checks for `Q01` at width `56`: chunks `736` to `751` of `1024` (`2 ^ 18` lanes each, `101` levels). -/

namespace KC.Q01W56.C46
open KC.Q01Lanes

theorem c736 : check 56 101 18 736 = true := by decide +kernel
theorem c737 : check 56 101 18 737 = true := by decide +kernel
theorem c738 : check 56 101 18 738 = true := by decide +kernel
theorem c739 : check 56 101 18 739 = true := by decide +kernel
theorem c740 : check 56 101 18 740 = true := by decide +kernel
theorem c741 : check 56 101 18 741 = true := by decide +kernel
theorem c742 : check 56 101 18 742 = true := by decide +kernel
theorem c743 : check 56 101 18 743 = true := by decide +kernel
theorem c744 : check 56 101 18 744 = true := by decide +kernel
theorem c745 : check 56 101 18 745 = true := by decide +kernel
theorem c746 : check 56 101 18 746 = true := by decide +kernel
theorem c747 : check 56 101 18 747 = true := by decide +kernel
theorem c748 : check 56 101 18 748 = true := by decide +kernel
theorem c749 : check 56 101 18 749 = true := by decide +kernel
theorem c750 : check 56 101 18 750 = true := by decide +kernel
theorem c751 : check 56 101 18 751 = true := by decide +kernel

theorem range : ChunksOK 56 101 18 736 16 :=
  (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c736) (chunksOK_one c737)) (chunksOK_append (chunksOK_one c738) (chunksOK_one c739))) (chunksOK_append (chunksOK_append (chunksOK_one c740) (chunksOK_one c741)) (chunksOK_append (chunksOK_one c742) (chunksOK_one c743)))) (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c744) (chunksOK_one c745)) (chunksOK_append (chunksOK_one c746) (chunksOK_one c747))) (chunksOK_append (chunksOK_append (chunksOK_one c748) (chunksOK_one c749)) (chunksOK_append (chunksOK_one c750) (chunksOK_one c751)))))

end KC.Q01W56.C46
