import KC.StripeFront

/-! Kernel-checked front-window cycles (window `32`, post-arrival horizon `31`). -/

namespace KC.StripeFront.StripeCycles2
open KC.StripeFront

theorem seg_5_0_0 : seg 32 31 1 1073741829 0 16384 0 5 0 = true := by decide +kernel
theorem seg_5_0_1 : seg 32 31 1 2147483653 0 16384 16384 1073741829 0 = true := by decide +kernel
theorem seg_5_0_2 : seg 32 31 1 3221225477 0 16384 32768 2147483653 0 = true := by decide +kernel
theorem seg_5_0_3 : seg 32 31 1 5 0 16384 49152 3221225477 0 = true := by decide +kernel

theorem cyc_5_0 : Cycle 32 31 5 0 65536 :=
  ⟨by decide, by decide, (path_append (path_append (path_append (seg_sound 32 31 1 1073741829 0 16384 0 5 0 seg_5_0_0) (seg_sound 32 31 1 2147483653 0 16384 16384 1073741829 0 seg_5_0_1)) (seg_sound 32 31 1 3221225477 0 16384 32768 2147483653 0 seg_5_0_2)) (seg_sound 32 31 1 5 0 16384 49152 3221225477 0 seg_5_0_3))⟩

end KC.StripeFront.StripeCycles2
