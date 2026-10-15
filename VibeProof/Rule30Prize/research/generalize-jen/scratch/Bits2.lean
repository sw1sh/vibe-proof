#check @Nat.testBit_two_pow_sub_one
#check @Nat.two_pow_pos
#check @Nat.zero_testBit
#check @Nat.testBit_one
#check @Nat.one_shiftLeft
#check @Nat.testBit_two_pow
#check @Nat.shiftLeft_eq
#check @Nat.pos_pow_of_pos
#check @Nat.mod_lt
#check @Bool.toNat
example (b : Bool) (i : Nat) : b.toNat.testBit i = (decide (i = 0) && b) := by
  cases b <;> cases i <;> simp [Bool.toNat, Nat.testBit_succ]
