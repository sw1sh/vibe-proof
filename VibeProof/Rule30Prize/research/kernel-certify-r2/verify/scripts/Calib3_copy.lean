namespace Calib3

/-- 7-round xor-scan with raw `Nat` primitives. -/
def xs (s i : Nat) : Nat := Nat.xor s (Nat.shiftRight s i)
def scan (g : Nat) : Nat := xs (xs (xs (xs (xs (xs (xs g 1) 2) 4) 8) 16) 32) 64

/-- `band a b = a && b`, `bor a b = a || b` via the recursor. -/
@[reducible] noncomputable def band (a b : Bool) : Bool := Bool.rec false b a
@[reducible] noncomputable def bor (a b : Bool) : Bool := Bool.rec b true a

noncomputable def dfs (W : Nat) (n : Nat) : Nat → Nat → Nat → Bool :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → Bool)
    (fun _ _ _ => false)
    (fun _ ih k A B =>
      let s := scan (Nat.lor A B)
      let m := Nat.sub (Nat.pow 2 k) 1
      let C1 := Nat.lor (Nat.xor s m) (Nat.add m 1)
      let late := Nat.blt W (Nat.add k 1)
      let br1 := bor (band late (Nat.beq (Nat.mod C1 2) 1)) (ih (Nat.add k 1) B C1)
      Bool.rec (band (bor (band late (Nat.beq (Nat.mod s 2) 1)) (ih (Nat.add k 1) B s)) br1)
        br1 (Nat.beq (Nat.mod k 2) 0))
    n

theorem c26 : dfs 28 50 0 0 0 = true := by decide +kernel

end Calib3
