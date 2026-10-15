import KC.Q01Lanes

/-! Kernel checks for `Q01` at width `56`: chunks `640` to `655` of `1024` (`2 ^ 18` lanes each, `101` levels). -/

namespace KC.Q01W56.C40
open KC.Q01Lanes

theorem c640 : check 56 101 18 640 = true := by decide +kernel
theorem c641 : check 56 101 18 641 = true := by decide +kernel
theorem c642 : check 56 101 18 642 = true := by decide +kernel
theorem c643 : check 56 101 18 643 = true := by decide +kernel
theorem c644 : check 56 101 18 644 = true := by decide +kernel
theorem c645 : check 56 101 18 645 = true := by decide +kernel
theorem c646 : check 56 101 18 646 = true := by decide +kernel
theorem c647 : check 56 101 18 647 = true := by decide +kernel
theorem c648 : check 56 101 18 648 = true := by decide +kernel
theorem c649 : check 56 101 18 649 = true := by decide +kernel
theorem c650 : check 56 101 18 650 = true := by decide +kernel
theorem c651 : check 56 101 18 651 = true := by decide +kernel
theorem c652 : check 56 101 18 652 = true := by decide +kernel
theorem c653 : check 56 101 18 653 = true := by decide +kernel
theorem c654 : check 56 101 18 654 = true := by decide +kernel
theorem c655 : check 56 101 18 655 = true := by decide +kernel

theorem range : ChunksOK 56 101 18 640 16 :=
  (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c640) (chunksOK_one c641)) (chunksOK_append (chunksOK_one c642) (chunksOK_one c643))) (chunksOK_append (chunksOK_append (chunksOK_one c644) (chunksOK_one c645)) (chunksOK_append (chunksOK_one c646) (chunksOK_one c647)))) (chunksOK_append (chunksOK_append (chunksOK_append (chunksOK_one c648) (chunksOK_one c649)) (chunksOK_append (chunksOK_one c650) (chunksOK_one c651))) (chunksOK_append (chunksOK_append (chunksOK_one c652) (chunksOK_one c653)) (chunksOK_append (chunksOK_one c654) (chunksOK_one c655)))))

end KC.Q01W56.C40
