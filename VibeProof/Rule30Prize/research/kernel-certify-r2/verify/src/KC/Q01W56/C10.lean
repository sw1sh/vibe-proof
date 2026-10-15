import KC.Q01Lanes

/-! Kernel checks for `Q01` at width `56`: chunks `160` to `175` of `1024` (`2 ^ 18` lanes each, `101` levels). -/

namespace KC.Q01W56.C10
open KC.Q01Lanes

theorem c160 : check 56 101 18 160 = true := by decide +kernel
theorem c161 : check 56 101 18 161 = true := by decide +kernel
theorem c162 : check 56 101 18 162 = true := by decide +kernel
theorem c163 : check 56 101 18 163 = true := by decide +kernel
theorem c164 : check 56 101 18 164 = true := by decide +kernel
theorem c165 : check 56 101 18 165 = true := by decide +kernel
theorem c166 : check 56 101 18 166 = true := by decide +kernel
theorem c167 : check 56 101 18 167 = true := by decide +kernel
theorem c168 : check 56 101 18 168 = true := by decide +kernel
theorem c169 : check 56 101 18 169 = true := by decide +kernel
theorem c170 : check 56 101 18 170 = true := by decide +kernel
theorem c171 : check 56 101 18 171 = true := by decide +kernel
theorem c172 : check 56 101 18 172 = true := by decide +kernel
theorem c173 : check 56 101 18 173 = true := by decide +kernel
theorem c174 : check 56 101 18 174 = true := by decide +kernel
theorem c175 : check 56 101 18 175 = true := by decide +kernel

theorem range : ChunksOK 56 101 18 160 16 :=
  (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c160) (chunksOK_one c161)) (chunksOK_append (chunksOK_one c162) (chunksOK_one c163))) (chunksOK_append (chunksOK_append (chunksOK_one c164) (chunksOK_one c165)) (chunksOK_append (chunksOK_one c166) (chunksOK_one c167)))) (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c168) (chunksOK_one c169)) (chunksOK_append (chunksOK_one c170) (chunksOK_one c171))) (chunksOK_append (chunksOK_append (chunksOK_one c172) (chunksOK_one c173)) (chunksOK_append (chunksOK_one c174) (chunksOK_one c175)))))

end KC.Q01W56.C10
