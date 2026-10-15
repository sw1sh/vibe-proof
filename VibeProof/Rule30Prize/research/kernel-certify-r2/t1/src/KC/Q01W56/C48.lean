import KC.Q01Lanes

/-! Kernel checks for `Q01` at width `56`: chunks `768` to `783` of `1024` (`2 ^ 18` lanes each, `101` levels). -/

namespace KC.Q01W56.C48
open KC.Q01Lanes

theorem c768 : check 56 101 18 768 = true := by decide +kernel
theorem c769 : check 56 101 18 769 = true := by decide +kernel
theorem c770 : check 56 101 18 770 = true := by decide +kernel
theorem c771 : check 56 101 18 771 = true := by decide +kernel
theorem c772 : check 56 101 18 772 = true := by decide +kernel
theorem c773 : check 56 101 18 773 = true := by decide +kernel
theorem c774 : check 56 101 18 774 = true := by decide +kernel
theorem c775 : check 56 101 18 775 = true := by decide +kernel
theorem c776 : check 56 101 18 776 = true := by decide +kernel
theorem c777 : check 56 101 18 777 = true := by decide +kernel
theorem c778 : check 56 101 18 778 = true := by decide +kernel
theorem c779 : check 56 101 18 779 = true := by decide +kernel
theorem c780 : check 56 101 18 780 = true := by decide +kernel
theorem c781 : check 56 101 18 781 = true := by decide +kernel
theorem c782 : check 56 101 18 782 = true := by decide +kernel
theorem c783 : check 56 101 18 783 = true := by decide +kernel

theorem range : ChunksOK 56 101 18 768 16 :=
  (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c768) (chunksOK_one c769)) (chunksOK_append (chunksOK_one c770) (chunksOK_one c771))) (chunksOK_append (chunksOK_append (chunksOK_one c772) (chunksOK_one c773)) (chunksOK_append (chunksOK_one c774) (chunksOK_one c775)))) (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c776) (chunksOK_one c777)) (chunksOK_append (chunksOK_one c778) (chunksOK_one c779))) (chunksOK_append (chunksOK_append (chunksOK_one c780) (chunksOK_one c781)) (chunksOK_append (chunksOK_one c782) (chunksOK_one c783)))))

end KC.Q01W56.C48
