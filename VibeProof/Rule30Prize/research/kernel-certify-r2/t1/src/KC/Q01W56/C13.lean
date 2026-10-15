import KC.Q01Lanes

/-! Kernel checks for `Q01` at width `56`: chunks `208` to `223` of `1024` (`2 ^ 18` lanes each, `101` levels). -/

namespace KC.Q01W56.C13
open KC.Q01Lanes

theorem c208 : check 56 101 18 208 = true := by decide +kernel
theorem c209 : check 56 101 18 209 = true := by decide +kernel
theorem c210 : check 56 101 18 210 = true := by decide +kernel
theorem c211 : check 56 101 18 211 = true := by decide +kernel
theorem c212 : check 56 101 18 212 = true := by decide +kernel
theorem c213 : check 56 101 18 213 = true := by decide +kernel
theorem c214 : check 56 101 18 214 = true := by decide +kernel
theorem c215 : check 56 101 18 215 = true := by decide +kernel
theorem c216 : check 56 101 18 216 = true := by decide +kernel
theorem c217 : check 56 101 18 217 = true := by decide +kernel
theorem c218 : check 56 101 18 218 = true := by decide +kernel
theorem c219 : check 56 101 18 219 = true := by decide +kernel
theorem c220 : check 56 101 18 220 = true := by decide +kernel
theorem c221 : check 56 101 18 221 = true := by decide +kernel
theorem c222 : check 56 101 18 222 = true := by decide +kernel
theorem c223 : check 56 101 18 223 = true := by decide +kernel

theorem range : ChunksOK 56 101 18 208 16 :=
  (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c208) (chunksOK_one c209)) (chunksOK_append (chunksOK_one c210) (chunksOK_one c211))) (chunksOK_append (chunksOK_append (chunksOK_one c212) (chunksOK_one c213)) (chunksOK_append (chunksOK_one c214) (chunksOK_one c215)))) (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c216) (chunksOK_one c217)) (chunksOK_append (chunksOK_one c218) (chunksOK_one c219))) (chunksOK_append (chunksOK_append (chunksOK_one c220) (chunksOK_one c221)) (chunksOK_append (chunksOK_one c222) (chunksOK_one c223)))))

end KC.Q01W56.C13
