namespace Calib2

/-- 7-round xor-scan: bit `j` becomes the xor of bits `j .. j + 127`. -/
def scan (g : Nat) : Nat :=
  let s := g ^^^ (g >>> 1)
  let s := s ^^^ (s >>> 2)
  let s := s ^^^ (s >>> 4)
  let s := s ^^^ (s >>> 8)
  let s := s ^^^ (s >>> 16)
  let s := s ^^^ (s >>> 32)
  s ^^^ (s >>> 64)

/-- one branch: new anti-diagonal `C`; dead if `W < k + 1` and `C` odd. -/
noncomputable def dfs (W : Nat) (n : Nat) : Nat → Nat → Nat → Bool :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → Bool)
    (fun _ _ _ => false)
    (fun _ ih k A B =>
      let s := scan (A ||| B)
      let m := 2 ^ k - 1
      let C1 := (s ^^^ m) ||| (m + 1)
      let br1 := (Nat.blt W (k + 1) && Nat.beq (C1 % 2) 1) || ih (k + 1) B C1
      cond (Nat.beq (k % 2) 0) br1
        (((Nat.blt W (k + 1) && Nat.beq (s % 2) 1) || ih (k + 1) B s) && br1))
    n

theorem c26 : dfs 26 46 0 0 0 = true := by decide +kernel

end Calib2
