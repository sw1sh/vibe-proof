import KC.Q01Lanes

/-! Kernel checks for `Q01` at width `52`: chunks `64` to `79` of `256` (`2 ^ 18` lanes each, `97` levels). -/

namespace KC.Q01W52.C4
open KC.Q01Lanes

theorem c64 : check 52 97 18 64 = true := by decide +kernel
theorem c65 : check 52 97 18 65 = true := by decide +kernel
theorem c66 : check 52 97 18 66 = true := by decide +kernel
theorem c67 : check 52 97 18 67 = true := by decide +kernel
theorem c68 : check 52 97 18 68 = true := by decide +kernel
theorem c69 : check 52 97 18 69 = true := by decide +kernel
theorem c70 : check 52 97 18 70 = true := by decide +kernel
theorem c71 : check 52 97 18 71 = true := by decide +kernel
theorem c72 : check 52 97 18 72 = true := by decide +kernel
theorem c73 : check 52 97 18 73 = true := by decide +kernel
theorem c74 : check 52 97 18 74 = true := by decide +kernel
theorem c75 : check 52 97 18 75 = true := by decide +kernel
theorem c76 : check 52 97 18 76 = true := by decide +kernel
theorem c77 : check 52 97 18 77 = true := by decide +kernel
theorem c78 : check 52 97 18 78 = true := by decide +kernel
theorem c79 : check 52 97 18 79 = true := by decide +kernel

theorem range : ChunksOK 52 97 18 64 16 :=
  (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c64) (chunksOK_one c65)) (chunksOK_append (chunksOK_one c66) (chunksOK_one c67))) (chunksOK_append (chunksOK_append (chunksOK_one c68) (chunksOK_one c69)) (chunksOK_append (chunksOK_one c70) (chunksOK_one c71)))) (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c72) (chunksOK_one c73)) (chunksOK_append (chunksOK_one c74) (chunksOK_one c75))) (chunksOK_append (chunksOK_append (chunksOK_one c76) (chunksOK_one c77)) (chunksOK_append (chunksOK_one c78) (chunksOK_one c79)))))

end KC.Q01W52.C4
