import KC.Q01Lanes

/-! Kernel checks for `Q01` at width `56`: chunks `976` to `991` of `1024` (`2 ^ 18` lanes each, `101` levels). -/

namespace KC.Q01W56.C61
open KC.Q01Lanes

theorem c976 : check 56 101 18 976 = true := by decide +kernel
theorem c977 : check 56 101 18 977 = true := by decide +kernel
theorem c978 : check 56 101 18 978 = true := by decide +kernel
theorem c979 : check 56 101 18 979 = true := by decide +kernel
theorem c980 : check 56 101 18 980 = true := by decide +kernel
theorem c981 : check 56 101 18 981 = true := by decide +kernel
theorem c982 : check 56 101 18 982 = true := by decide +kernel
theorem c983 : check 56 101 18 983 = true := by decide +kernel
theorem c984 : check 56 101 18 984 = true := by decide +kernel
theorem c985 : check 56 101 18 985 = true := by decide +kernel
theorem c986 : check 56 101 18 986 = true := by decide +kernel
theorem c987 : check 56 101 18 987 = true := by decide +kernel
theorem c988 : check 56 101 18 988 = true := by decide +kernel
theorem c989 : check 56 101 18 989 = true := by decide +kernel
theorem c990 : check 56 101 18 990 = true := by decide +kernel
theorem c991 : check 56 101 18 991 = true := by decide +kernel

theorem range : ChunksOK 56 101 18 976 16 :=
  (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c976) (chunksOK_one c977)) (chunksOK_append (chunksOK_one c978) (chunksOK_one c979))) (chunksOK_append (chunksOK_append (chunksOK_one c980) (chunksOK_one c981)) (chunksOK_append (chunksOK_one c982) (chunksOK_one c983)))) (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c984) (chunksOK_one c985)) (chunksOK_append (chunksOK_one c986) (chunksOK_one c987))) (chunksOK_append (chunksOK_append (chunksOK_one c988) (chunksOK_one c989)) (chunksOK_append (chunksOK_one c990) (chunksOK_one c991)))))

end KC.Q01W56.C61
