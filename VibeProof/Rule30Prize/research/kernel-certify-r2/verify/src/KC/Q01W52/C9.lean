import KC.Q01Lanes

/-! Kernel checks for `Q01` at width `52`: chunks `144` to `159` of `256` (`2 ^ 18` lanes each, `97` levels). -/

namespace KC.Q01W52.C9
open KC.Q01Lanes

theorem c144 : check 52 97 18 144 = true := by decide +kernel
theorem c145 : check 52 97 18 145 = true := by decide +kernel
theorem c146 : check 52 97 18 146 = true := by decide +kernel
theorem c147 : check 52 97 18 147 = true := by decide +kernel
theorem c148 : check 52 97 18 148 = true := by decide +kernel
theorem c149 : check 52 97 18 149 = true := by decide +kernel
theorem c150 : check 52 97 18 150 = true := by decide +kernel
theorem c151 : check 52 97 18 151 = true := by decide +kernel
theorem c152 : check 52 97 18 152 = true := by decide +kernel
theorem c153 : check 52 97 18 153 = true := by decide +kernel
theorem c154 : check 52 97 18 154 = true := by decide +kernel
theorem c155 : check 52 97 18 155 = true := by decide +kernel
theorem c156 : check 52 97 18 156 = true := by decide +kernel
theorem c157 : check 52 97 18 157 = true := by decide +kernel
theorem c158 : check 52 97 18 158 = true := by decide +kernel
theorem c159 : check 52 97 18 159 = true := by decide +kernel

theorem range : ChunksOK 52 97 18 144 16 :=
  (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c144) (chunksOK_one c145)) (chunksOK_append (chunksOK_one c146) (chunksOK_one c147))) (chunksOK_append (chunksOK_append (chunksOK_one c148) (chunksOK_one c149)) (chunksOK_append (chunksOK_one c150) (chunksOK_one c151)))) (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c152) (chunksOK_one c153)) (chunksOK_append (chunksOK_one c154) (chunksOK_one c155))) (chunksOK_append (chunksOK_append (chunksOK_one c156) (chunksOK_one c157)) (chunksOK_append (chunksOK_one c158) (chunksOK_one c159)))))

end KC.Q01W52.C9
