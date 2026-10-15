import KC.Q01Lanes

/-! Kernel checks for `Q01` at width `56`: chunks `880` to `895` of `1024` (`2 ^ 18` lanes each, `101` levels). -/

namespace KC.Q01W56.C55
open KC.Q01Lanes

theorem c880 : check 56 101 18 880 = true := by decide +kernel
theorem c881 : check 56 101 18 881 = true := by decide +kernel
theorem c882 : check 56 101 18 882 = true := by decide +kernel
theorem c883 : check 56 101 18 883 = true := by decide +kernel
theorem c884 : check 56 101 18 884 = true := by decide +kernel
theorem c885 : check 56 101 18 885 = true := by decide +kernel
theorem c886 : check 56 101 18 886 = true := by decide +kernel
theorem c887 : check 56 101 18 887 = true := by decide +kernel
theorem c888 : check 56 101 18 888 = true := by decide +kernel
theorem c889 : check 56 101 18 889 = true := by decide +kernel
theorem c890 : check 56 101 18 890 = true := by decide +kernel
theorem c891 : check 56 101 18 891 = true := by decide +kernel
theorem c892 : check 56 101 18 892 = true := by decide +kernel
theorem c893 : check 56 101 18 893 = true := by decide +kernel
theorem c894 : check 56 101 18 894 = true := by decide +kernel
theorem c895 : check 56 101 18 895 = true := by decide +kernel

theorem range : ChunksOK 56 101 18 880 16 :=
  (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c880) (chunksOK_one c881)) (chunksOK_append (chunksOK_one c882) (chunksOK_one c883))) (chunksOK_append (chunksOK_append (chunksOK_one c884) (chunksOK_one c885)) (chunksOK_append (chunksOK_one c886) (chunksOK_one c887)))) (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c888) (chunksOK_one c889)) (chunksOK_append (chunksOK_one c890) (chunksOK_one c891))) (chunksOK_append (chunksOK_append (chunksOK_one c892) (chunksOK_one c893)) (chunksOK_append (chunksOK_one c894) (chunksOK_one c895)))))

end KC.Q01W56.C55
