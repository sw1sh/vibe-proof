import KC.Q01Lanes

/-! Kernel checks for `Q01` at width `52`: chunks `96` to `111` of `256` (`2 ^ 18` lanes each, `97` levels). -/

namespace KC.Q01W52.C6
open KC.Q01Lanes

theorem c96 : check 52 97 18 96 = true := by decide +kernel
theorem c97 : check 52 97 18 97 = true := by decide +kernel
theorem c98 : check 52 97 18 98 = true := by decide +kernel
theorem c99 : check 52 97 18 99 = true := by decide +kernel
theorem c100 : check 52 97 18 100 = true := by decide +kernel
theorem c101 : check 52 97 18 101 = true := by decide +kernel
theorem c102 : check 52 97 18 102 = true := by decide +kernel
theorem c103 : check 52 97 18 103 = true := by decide +kernel
theorem c104 : check 52 97 18 104 = true := by decide +kernel
theorem c105 : check 52 97 18 105 = true := by decide +kernel
theorem c106 : check 52 97 18 106 = true := by decide +kernel
theorem c107 : check 52 97 18 107 = true := by decide +kernel
theorem c108 : check 52 97 18 108 = true := by decide +kernel
theorem c109 : check 52 97 18 109 = true := by decide +kernel
theorem c110 : check 52 97 18 110 = true := by decide +kernel
theorem c111 : check 52 97 18 111 = true := by decide +kernel

theorem range : ChunksOK 52 97 18 96 16 :=
  (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c96) (chunksOK_one c97)) (chunksOK_append (chunksOK_one c98) (chunksOK_one c99))) (chunksOK_append (chunksOK_append (chunksOK_one c100) (chunksOK_one c101)) (chunksOK_append (chunksOK_one c102) (chunksOK_one c103)))) (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c104) (chunksOK_one c105)) (chunksOK_append (chunksOK_one c106) (chunksOK_one c107))) (chunksOK_append (chunksOK_append (chunksOK_one c108) (chunksOK_one c109)) (chunksOK_append (chunksOK_one c110) (chunksOK_one c111)))))

end KC.Q01W52.C6
