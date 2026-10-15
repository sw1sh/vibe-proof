import KC.Q01Lanes

/-! Kernel checks for `Q01` at width `56`: chunks `112` to `127` of `1024` (`2 ^ 18` lanes each, `101` levels). -/

namespace KC.Q01W56.C7
open KC.Q01Lanes

theorem c112 : check 56 101 18 112 = true := by decide +kernel
theorem c113 : check 56 101 18 113 = true := by decide +kernel
theorem c114 : check 56 101 18 114 = true := by decide +kernel
theorem c115 : check 56 101 18 115 = true := by decide +kernel
theorem c116 : check 56 101 18 116 = true := by decide +kernel
theorem c117 : check 56 101 18 117 = true := by decide +kernel
theorem c118 : check 56 101 18 118 = true := by decide +kernel
theorem c119 : check 56 101 18 119 = true := by decide +kernel
theorem c120 : check 56 101 18 120 = true := by decide +kernel
theorem c121 : check 56 101 18 121 = true := by decide +kernel
theorem c122 : check 56 101 18 122 = true := by decide +kernel
theorem c123 : check 56 101 18 123 = true := by decide +kernel
theorem c124 : check 56 101 18 124 = true := by decide +kernel
theorem c125 : check 56 101 18 125 = true := by decide +kernel
theorem c126 : check 56 101 18 126 = true := by decide +kernel
theorem c127 : check 56 101 18 127 = true := by decide +kernel

theorem range : ChunksOK 56 101 18 112 16 :=
  (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c112) (chunksOK_one c113)) (chunksOK_append (chunksOK_one c114) (chunksOK_one c115))) (chunksOK_append (chunksOK_append (chunksOK_one c116) (chunksOK_one c117)) (chunksOK_append (chunksOK_one c118) (chunksOK_one c119)))) (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c120) (chunksOK_one c121)) (chunksOK_append (chunksOK_one c122) (chunksOK_one c123))) (chunksOK_append (chunksOK_append (chunksOK_one c124) (chunksOK_one c125)) (chunksOK_append (chunksOK_one c126) (chunksOK_one c127)))))

end KC.Q01W56.C7
