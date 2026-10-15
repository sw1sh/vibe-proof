import KC.Q01Lanes

/-! Kernel checks for `Q01` at width `56`: chunks `176` to `191` of `1024` (`2 ^ 18` lanes each, `101` levels). -/

namespace KC.Q01W56.C11
open KC.Q01Lanes

theorem c176 : check 56 101 18 176 = true := by decide +kernel
theorem c177 : check 56 101 18 177 = true := by decide +kernel
theorem c178 : check 56 101 18 178 = true := by decide +kernel
theorem c179 : check 56 101 18 179 = true := by decide +kernel
theorem c180 : check 56 101 18 180 = true := by decide +kernel
theorem c181 : check 56 101 18 181 = true := by decide +kernel
theorem c182 : check 56 101 18 182 = true := by decide +kernel
theorem c183 : check 56 101 18 183 = true := by decide +kernel
theorem c184 : check 56 101 18 184 = true := by decide +kernel
theorem c185 : check 56 101 18 185 = true := by decide +kernel
theorem c186 : check 56 101 18 186 = true := by decide +kernel
theorem c187 : check 56 101 18 187 = true := by decide +kernel
theorem c188 : check 56 101 18 188 = true := by decide +kernel
theorem c189 : check 56 101 18 189 = true := by decide +kernel
theorem c190 : check 56 101 18 190 = true := by decide +kernel
theorem c191 : check 56 101 18 191 = true := by decide +kernel

theorem range : ChunksOK 56 101 18 176 16 :=
  (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c176) (chunksOK_one c177)) (chunksOK_append (chunksOK_one c178) (chunksOK_one c179))) (chunksOK_append (chunksOK_append (chunksOK_one c180) (chunksOK_one c181)) (chunksOK_append (chunksOK_one c182) (chunksOK_one c183)))) (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c184) (chunksOK_one c185)) (chunksOK_append (chunksOK_one c186) (chunksOK_one c187))) (chunksOK_append (chunksOK_append (chunksOK_one c188) (chunksOK_one c189)) (chunksOK_append (chunksOK_one c190) (chunksOK_one c191)))))

end KC.Q01W56.C11
