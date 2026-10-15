import KC.Q01Lanes

/-! Kernel checks for `Q01` at width `56`: chunks `672` to `687` of `1024` (`2 ^ 18` lanes each, `101` levels). -/

namespace KC.Q01W56.C42
open KC.Q01Lanes

theorem c672 : check 56 101 18 672 = true := by decide +kernel
theorem c673 : check 56 101 18 673 = true := by decide +kernel
theorem c674 : check 56 101 18 674 = true := by decide +kernel
theorem c675 : check 56 101 18 675 = true := by decide +kernel
theorem c676 : check 56 101 18 676 = true := by decide +kernel
theorem c677 : check 56 101 18 677 = true := by decide +kernel
theorem c678 : check 56 101 18 678 = true := by decide +kernel
theorem c679 : check 56 101 18 679 = true := by decide +kernel
theorem c680 : check 56 101 18 680 = true := by decide +kernel
theorem c681 : check 56 101 18 681 = true := by decide +kernel
theorem c682 : check 56 101 18 682 = true := by decide +kernel
theorem c683 : check 56 101 18 683 = true := by decide +kernel
theorem c684 : check 56 101 18 684 = true := by decide +kernel
theorem c685 : check 56 101 18 685 = true := by decide +kernel
theorem c686 : check 56 101 18 686 = true := by decide +kernel
theorem c687 : check 56 101 18 687 = true := by decide +kernel

theorem range : ChunksOK 56 101 18 672 16 :=
  (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c672) (chunksOK_one c673)) (chunksOK_append (chunksOK_one c674) (chunksOK_one c675))) (chunksOK_append (chunksOK_append (chunksOK_one c676) (chunksOK_one c677)) (chunksOK_append (chunksOK_one c678) (chunksOK_one c679)))) (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c680) (chunksOK_one c681)) (chunksOK_append (chunksOK_one c682) (chunksOK_one c683))) (chunksOK_append (chunksOK_append (chunksOK_one c684) (chunksOK_one c685)) (chunksOK_append (chunksOK_one c686) (chunksOK_one c687)))))

end KC.Q01W56.C42
