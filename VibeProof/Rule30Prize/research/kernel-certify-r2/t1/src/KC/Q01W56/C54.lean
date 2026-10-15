import KC.Q01Lanes

/-! Kernel checks for `Q01` at width `56`: chunks `864` to `879` of `1024` (`2 ^ 18` lanes each, `101` levels). -/

namespace KC.Q01W56.C54
open KC.Q01Lanes

theorem c864 : check 56 101 18 864 = true := by decide +kernel
theorem c865 : check 56 101 18 865 = true := by decide +kernel
theorem c866 : check 56 101 18 866 = true := by decide +kernel
theorem c867 : check 56 101 18 867 = true := by decide +kernel
theorem c868 : check 56 101 18 868 = true := by decide +kernel
theorem c869 : check 56 101 18 869 = true := by decide +kernel
theorem c870 : check 56 101 18 870 = true := by decide +kernel
theorem c871 : check 56 101 18 871 = true := by decide +kernel
theorem c872 : check 56 101 18 872 = true := by decide +kernel
theorem c873 : check 56 101 18 873 = true := by decide +kernel
theorem c874 : check 56 101 18 874 = true := by decide +kernel
theorem c875 : check 56 101 18 875 = true := by decide +kernel
theorem c876 : check 56 101 18 876 = true := by decide +kernel
theorem c877 : check 56 101 18 877 = true := by decide +kernel
theorem c878 : check 56 101 18 878 = true := by decide +kernel
theorem c879 : check 56 101 18 879 = true := by decide +kernel

theorem range : ChunksOK 56 101 18 864 16 :=
  (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c864) (chunksOK_one c865)) (chunksOK_append (chunksOK_one c866) (chunksOK_one c867))) (chunksOK_append (chunksOK_append (chunksOK_one c868) (chunksOK_one c869)) (chunksOK_append (chunksOK_one c870) (chunksOK_one c871)))) (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c872) (chunksOK_one c873)) (chunksOK_append (chunksOK_one c874) (chunksOK_one c875))) (chunksOK_append (chunksOK_append (chunksOK_one c876) (chunksOK_one c877)) (chunksOK_append (chunksOK_one c878) (chunksOK_one c879)))))

end KC.Q01W56.C54
