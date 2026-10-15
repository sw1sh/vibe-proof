import KC.Q01Lanes

/-! Kernel checks for `Q01` at width `52`: chunks `128` to `143` of `256` (`2 ^ 18` lanes each, `97` levels). -/

namespace KC.Q01W52.C8
open KC.Q01Lanes

theorem c128 : check 52 97 18 128 = true := by decide +kernel
theorem c129 : check 52 97 18 129 = true := by decide +kernel
theorem c130 : check 52 97 18 130 = true := by decide +kernel
theorem c131 : check 52 97 18 131 = true := by decide +kernel
theorem c132 : check 52 97 18 132 = true := by decide +kernel
theorem c133 : check 52 97 18 133 = true := by decide +kernel
theorem c134 : check 52 97 18 134 = true := by decide +kernel
theorem c135 : check 52 97 18 135 = true := by decide +kernel
theorem c136 : check 52 97 18 136 = true := by decide +kernel
theorem c137 : check 52 97 18 137 = true := by decide +kernel
theorem c138 : check 52 97 18 138 = true := by decide +kernel
theorem c139 : check 52 97 18 139 = true := by decide +kernel
theorem c140 : check 52 97 18 140 = true := by decide +kernel
theorem c141 : check 52 97 18 141 = true := by decide +kernel
theorem c142 : check 52 97 18 142 = true := by decide +kernel
theorem c143 : check 52 97 18 143 = true := by decide +kernel

theorem range : ChunksOK 52 97 18 128 16 :=
  (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c128) (chunksOK_one c129)) (chunksOK_append (chunksOK_one c130) (chunksOK_one c131))) (chunksOK_append (chunksOK_append (chunksOK_one c132) (chunksOK_one c133)) (chunksOK_append (chunksOK_one c134) (chunksOK_one c135)))) (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c136) (chunksOK_one c137)) (chunksOK_append (chunksOK_one c138) (chunksOK_one c139))) (chunksOK_append (chunksOK_append (chunksOK_one c140) (chunksOK_one c141)) (chunksOK_append (chunksOK_one c142) (chunksOK_one c143)))))

end KC.Q01W52.C8
