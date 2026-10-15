import KC.Q01Lanes

/-! Kernel checks for `Q01` at width `56`: chunks `800` to `815` of `1024` (`2 ^ 18` lanes each, `101` levels). -/

namespace KC.Q01W56.C50
open KC.Q01Lanes

theorem c800 : check 56 101 18 800 = true := by decide +kernel
theorem c801 : check 56 101 18 801 = true := by decide +kernel
theorem c802 : check 56 101 18 802 = true := by decide +kernel
theorem c803 : check 56 101 18 803 = true := by decide +kernel
theorem c804 : check 56 101 18 804 = true := by decide +kernel
theorem c805 : check 56 101 18 805 = true := by decide +kernel
theorem c806 : check 56 101 18 806 = true := by decide +kernel
theorem c807 : check 56 101 18 807 = true := by decide +kernel
theorem c808 : check 56 101 18 808 = true := by decide +kernel
theorem c809 : check 56 101 18 809 = true := by decide +kernel
theorem c810 : check 56 101 18 810 = true := by decide +kernel
theorem c811 : check 56 101 18 811 = true := by decide +kernel
theorem c812 : check 56 101 18 812 = true := by decide +kernel
theorem c813 : check 56 101 18 813 = true := by decide +kernel
theorem c814 : check 56 101 18 814 = true := by decide +kernel
theorem c815 : check 56 101 18 815 = true := by decide +kernel

theorem range : ChunksOK 56 101 18 800 16 :=
  (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c800) (chunksOK_one c801)) (chunksOK_append (chunksOK_one c802) (chunksOK_one c803))) (chunksOK_append (chunksOK_append (chunksOK_one c804) (chunksOK_one c805)) (chunksOK_append (chunksOK_one c806) (chunksOK_one c807)))) (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c808) (chunksOK_one c809)) (chunksOK_append (chunksOK_one c810) (chunksOK_one c811))) (chunksOK_append (chunksOK_append (chunksOK_one c812) (chunksOK_one c813)) (chunksOK_append (chunksOK_one c814) (chunksOK_one c815)))))

end KC.Q01W56.C50
