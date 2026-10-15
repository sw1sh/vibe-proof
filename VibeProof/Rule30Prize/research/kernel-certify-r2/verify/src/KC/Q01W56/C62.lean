import KC.Q01Lanes

/-! Kernel checks for `Q01` at width `56`: chunks `992` to `1007` of `1024` (`2 ^ 18` lanes each, `101` levels). -/

namespace KC.Q01W56.C62
open KC.Q01Lanes

theorem c992 : check 56 101 18 992 = true := by decide +kernel
theorem c993 : check 56 101 18 993 = true := by decide +kernel
theorem c994 : check 56 101 18 994 = true := by decide +kernel
theorem c995 : check 56 101 18 995 = true := by decide +kernel
theorem c996 : check 56 101 18 996 = true := by decide +kernel
theorem c997 : check 56 101 18 997 = true := by decide +kernel
theorem c998 : check 56 101 18 998 = true := by decide +kernel
theorem c999 : check 56 101 18 999 = true := by decide +kernel
theorem c1000 : check 56 101 18 1000 = true := by decide +kernel
theorem c1001 : check 56 101 18 1001 = true := by decide +kernel
theorem c1002 : check 56 101 18 1002 = true := by decide +kernel
theorem c1003 : check 56 101 18 1003 = true := by decide +kernel
theorem c1004 : check 56 101 18 1004 = true := by decide +kernel
theorem c1005 : check 56 101 18 1005 = true := by decide +kernel
theorem c1006 : check 56 101 18 1006 = true := by decide +kernel
theorem c1007 : check 56 101 18 1007 = true := by decide +kernel

theorem range : ChunksOK 56 101 18 992 16 :=
  (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c992) (chunksOK_one c993)) (chunksOK_append (chunksOK_one c994) (chunksOK_one c995))) (chunksOK_append (chunksOK_append (chunksOK_one c996) (chunksOK_one c997)) (chunksOK_append (chunksOK_one c998) (chunksOK_one c999)))) (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c1000) (chunksOK_one c1001)) (chunksOK_append (chunksOK_one c1002) (chunksOK_one c1003))) (chunksOK_append (chunksOK_append (chunksOK_one c1004) (chunksOK_one c1005)) (chunksOK_append (chunksOK_one c1006) (chunksOK_one c1007)))))

end KC.Q01W56.C62
