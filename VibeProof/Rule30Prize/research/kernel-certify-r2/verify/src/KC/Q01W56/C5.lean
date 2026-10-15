import KC.Q01Lanes

/-! Kernel checks for `Q01` at width `56`: chunks `80` to `95` of `1024` (`2 ^ 18` lanes each, `101` levels). -/

namespace KC.Q01W56.C5
open KC.Q01Lanes

theorem c80 : check 56 101 18 80 = true := by decide +kernel
theorem c81 : check 56 101 18 81 = true := by decide +kernel
theorem c82 : check 56 101 18 82 = true := by decide +kernel
theorem c83 : check 56 101 18 83 = true := by decide +kernel
theorem c84 : check 56 101 18 84 = true := by decide +kernel
theorem c85 : check 56 101 18 85 = true := by decide +kernel
theorem c86 : check 56 101 18 86 = true := by decide +kernel
theorem c87 : check 56 101 18 87 = true := by decide +kernel
theorem c88 : check 56 101 18 88 = true := by decide +kernel
theorem c89 : check 56 101 18 89 = true := by decide +kernel
theorem c90 : check 56 101 18 90 = true := by decide +kernel
theorem c91 : check 56 101 18 91 = true := by decide +kernel
theorem c92 : check 56 101 18 92 = true := by decide +kernel
theorem c93 : check 56 101 18 93 = true := by decide +kernel
theorem c94 : check 56 101 18 94 = true := by decide +kernel
theorem c95 : check 56 101 18 95 = true := by decide +kernel

theorem range : ChunksOK 56 101 18 80 16 :=
  (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c80) (chunksOK_one c81)) (chunksOK_append (chunksOK_one c82) (chunksOK_one c83))) (chunksOK_append (chunksOK_append (chunksOK_one c84) (chunksOK_one c85)) (chunksOK_append (chunksOK_one c86) (chunksOK_one c87)))) (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c88) (chunksOK_one c89)) (chunksOK_append (chunksOK_one c90) (chunksOK_one c91))) (chunksOK_append (chunksOK_append (chunksOK_one c92) (chunksOK_one c93)) (chunksOK_append (chunksOK_one c94) (chunksOK_one c95)))))

end KC.Q01W56.C5
