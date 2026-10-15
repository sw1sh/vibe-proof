example (x : Nat → Bool) (d i : Nat) : ((List.range d).map x).getD i false = if i < d then x i else false := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map]
  by_cases h : i < d
  · rw [if_pos h, List.getElem?_range h]; rfl
  · rw [if_neg h, List.getElem?_eq_none (by simp; omega)]; rfl
