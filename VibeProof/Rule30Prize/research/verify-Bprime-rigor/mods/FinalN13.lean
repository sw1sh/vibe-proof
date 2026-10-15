import DetBaseV
import PF_0000100
import PT_0000100
import PF_0010010
import PT_0010010
import PF_0010110
import PT_0010110
import PF_0100100
import PT_0100100
import PF_0101000
import PT_0101000
import PF_0110000
import PT_0110000
import PF_0110010
import PT_0110010
import PF_0110110
import PT_0110110
namespace AbsorbRightV
open Ruliology.CellularAutomata.Rule30Jen
theorem det_0000100 : Determined [false, false, false, false, true, false, false] 2 = true := by
  rw [Determined_eq]
  show (allLists (12 + 1)).all (G [false, false, false, false, true, false, false] 2) = true
  rw [all_allLists_succ, pF_0000100, pT_0000100]
  rfl
#print axioms det_0000100
theorem det_0010010 : Determined [false, false, true, false, false, true, false] 2 = true := by
  rw [Determined_eq]
  show (allLists (12 + 1)).all (G [false, false, true, false, false, true, false] 2) = true
  rw [all_allLists_succ, pF_0010010, pT_0010010]
  rfl
#print axioms det_0010010
theorem det_0010110 : Determined [false, false, true, false, true, true, false] 2 = true := by
  rw [Determined_eq]
  show (allLists (12 + 1)).all (G [false, false, true, false, true, true, false] 2) = true
  rw [all_allLists_succ, pF_0010110, pT_0010110]
  rfl
#print axioms det_0010110
theorem det_0100100 : Determined [false, true, false, false, true, false, false] 2 = true := by
  rw [Determined_eq]
  show (allLists (12 + 1)).all (G [false, true, false, false, true, false, false] 2) = true
  rw [all_allLists_succ, pF_0100100, pT_0100100]
  rfl
#print axioms det_0100100
theorem det_0101000 : Determined [false, true, false, true, false, false, false] 2 = true := by
  rw [Determined_eq]
  show (allLists (12 + 1)).all (G [false, true, false, true, false, false, false] 2) = true
  rw [all_allLists_succ, pF_0101000, pT_0101000]
  rfl
#print axioms det_0101000
theorem det_0110000 : Determined [false, true, true, false, false, false, false] 2 = true := by
  rw [Determined_eq]
  show (allLists (12 + 1)).all (G [false, true, true, false, false, false, false] 2) = true
  rw [all_allLists_succ, pF_0110000, pT_0110000]
  rfl
#print axioms det_0110000
theorem det_0110010 : Determined [false, true, true, false, false, true, false] 2 = true := by
  rw [Determined_eq]
  show (allLists (12 + 1)).all (G [false, true, true, false, false, true, false] 2) = true
  rw [all_allLists_succ, pF_0110010, pT_0110010]
  rfl
#print axioms det_0110010
theorem det_0110110 : Determined [false, true, true, false, true, true, false] 2 = true := by
  rw [Determined_eq]
  show (allLists (12 + 1)).all (G [false, true, true, false, true, true, false] 2) = true
  rw [all_allLists_succ, pF_0110110, pT_0110110]
  rfl
#print axioms det_0110110
end AbsorbRightV
