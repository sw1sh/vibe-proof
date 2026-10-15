import KC.Q01Lanes

/-! Kernel checks for `Q01` at width `56`: chunks `704` to `719` of `1024` (`2 ^ 18` lanes each, `101` levels). -/

namespace KC.Q01W56.C44
open KC.Q01Lanes

theorem c704 : check 56 101 18 704 = true := by decide +kernel
theorem c705 : check 56 101 18 705 = true := by decide +kernel
theorem c706 : check 56 101 18 706 = true := by decide +kernel
theorem c707 : check 56 101 18 707 = true := by decide +kernel
theorem c708 : check 56 101 18 708 = true := by decide +kernel
theorem c709 : check 56 101 18 709 = true := by decide +kernel
theorem c710 : check 56 101 18 710 = true := by decide +kernel
theorem c711 : check 56 101 18 711 = true := by decide +kernel
theorem c712 : check 56 101 18 712 = true := by decide +kernel
theorem c713 : check 56 101 18 713 = true := by decide +kernel
theorem c714 : check 56 101 18 714 = true := by decide +kernel
theorem c715 : check 56 101 18 715 = true := by decide +kernel
theorem c716 : check 56 101 18 716 = true := by decide +kernel
theorem c717 : check 56 101 18 717 = true := by decide +kernel
theorem c718 : check 56 101 18 718 = true := by decide +kernel
theorem c719 : check 56 101 18 719 = true := by decide +kernel

theorem range : ChunksOK 56 101 18 704 16 :=
  (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c704) (chunksOK_one c705)) (chunksOK_append (chunksOK_one c706) (chunksOK_one c707))) (chunksOK_append (chunksOK_append (chunksOK_one c708) (chunksOK_one c709)) (chunksOK_append (chunksOK_one c710) (chunksOK_one c711)))) (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c712) (chunksOK_one c713)) (chunksOK_append (chunksOK_one c714) (chunksOK_one c715))) (chunksOK_append (chunksOK_append (chunksOK_one c716) (chunksOK_one c717)) (chunksOK_append (chunksOK_one c718) (chunksOK_one c719)))))

end KC.Q01W56.C44
