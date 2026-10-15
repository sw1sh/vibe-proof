#check @Nat.gcd.induction
#check @Nat.gcd_rec
#check @Nat.gcd_zero_left
#check @Nat.gcd_dvd_left
#check @Nat.gcd_dvd_right
#check @Nat.mod_add_div
#check @Nat.mul_mod
#check @Nat.pow_succ
#check @Nat.mul_left_comm
#check @Nat.eq_one_of_dvd_one
#check @Nat.dvd_one
#check @Nat.one_dvd
#check @Nat.lt_succ_self
#check @Nat.Coprime
example (k d c : Nat) (hc : 2 ^ k * 2 = 2 * (d * c)) : 2 ^ k = d * c := by omega
example (k : Nat) : 2 ^ k * 2 = 2 ^ k + 2 ^ k := by omega
