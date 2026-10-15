import KC.Q01Lanes

/-! Kernel checks for `Q01` at width `56`: chunks `928` to `943` of `1024` (`2 ^ 18` lanes each, `101` levels). -/

namespace KC.Q01W56.C58
open KC.Q01Lanes

theorem c928 : check 56 101 18 928 = true := by decide +kernel
theorem c929 : check 56 101 18 929 = true := by decide +kernel
theorem c930 : check 56 101 18 930 = true := by decide +kernel
theorem c931 : check 56 101 18 931 = true := by decide +kernel
theorem c932 : check 56 101 18 932 = true := by decide +kernel
theorem c933 : check 56 101 18 933 = true := by decide +kernel
theorem c934 : check 56 101 18 934 = true := by decide +kernel
theorem c935 : check 56 101 18 935 = true := by decide +kernel
theorem c936 : check 56 101 18 936 = true := by decide +kernel
theorem c937 : check 56 101 18 937 = true := by decide +kernel
theorem c938 : check 56 101 18 938 = true := by decide +kernel
theorem c939 : check 56 101 18 939 = true := by decide +kernel
theorem c940 : check 56 101 18 940 = true := by decide +kernel
theorem c941 : check 56 101 18 941 = true := by decide +kernel
theorem c942 : check 56 101 18 942 = true := by decide +kernel
theorem c943 : check 56 101 18 943 = true := by decide +kernel

theorem range : ChunksOK 56 101 18 928 16 :=
  (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c928) (chunksOK_one c929)) (chunksOK_append (chunksOK_one c930) (chunksOK_one c931))) (chunksOK_append (chunksOK_append (chunksOK_one c932) (chunksOK_one c933)) (chunksOK_append (chunksOK_one c934) (chunksOK_one c935)))) (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c936) (chunksOK_one c937)) (chunksOK_append (chunksOK_one c938) (chunksOK_one c939))) (chunksOK_append (chunksOK_append (chunksOK_one c940) (chunksOK_one c941)) (chunksOK_append (chunksOK_one c942) (chunksOK_one c943)))))

end KC.Q01W56.C58
