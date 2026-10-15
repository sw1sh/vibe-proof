namespace ZBL

def s (k : Nat) : Bool := k % 2 == 1

theorem s_succ (k : Nat) : s (k + 1) = !s k := by
  unfold s
  rcases Nat.mod_two_eq_zero_or_one k with h | h
  · have : (k + 1) % 2 = 1 := by omega
    simp [h, this]
  · have : (k + 1) % 2 = 0 := by omega
    simp [h, this]

theorem s_add_two (k : Nat) : s (k + 2) = s k := by
  rw [s_succ, s_succ]; simp

theorem s_or (k : Nat) : (s (k + 1) || s k) = true := by
  rw [s_succ]; cases s k <;> rfl

theorem s_zero : s 0 = false := rfl
theorem s_one : s 1 = true := rfl
theorem s_odd {k : Nat} (h : k % 2 = 1) : s k = true := by unfold s; simp [h]
theorem s_even {k : Nat} (h : k % 2 = 0) : s k = false := by unfold s; simp [h]

end ZBL
