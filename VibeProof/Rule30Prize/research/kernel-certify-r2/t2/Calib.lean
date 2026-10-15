namespace CalibF

def fstep (K W fp : Nat) : Nat :=
  Nat.land (Nat.xor W (Nat.lor (Nat.lor (Nat.shiftLeft W 1) (Nat.sub 1 fp))
      (Nat.lor (Nat.lor (Nat.shiftLeft W 2) (Nat.shiftLeft (Nat.sub 1 fp) 1)) fp)))
    (Nat.sub (Nat.pow 2 K) 1)

def pstepN (x : Nat) : Nat := Nat.xor (Nat.shiftRight x 1) (Nat.lor x (Nat.shiftLeft x 1))

noncomputable def band (a b : Bool) : Bool := Bool.rec false b a

noncomputable def sig (fuel : Nat) : Nat → Nat → Bool :=
  Nat.rec (motive := fun _ => Nat → Nat → Bool) (fun _ _ => false)
    (fun _ ih r x => Bool.rec (ih (Nat.add r 1) (pstepN x)) true
      (band (Nat.beq (Nat.mod r 2) 0) (Nat.beq (Nat.mod x 2) 0))) fuel

noncomputable def seg (K S q Wb pb : Nat) (fuel : Nat) : Nat → Nat → Nat → Bool :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → Bool)
    (fun _ W fp => band (Nat.beq W Wb) (Nat.beq fp pb))
    (fun _ ih r W fp => band (Bool.rec true (sig (Nat.add S 1) r W) (Nat.beq (Nat.mod r 2) q))
      (ih (Nat.add r 1) (fstep K W fp) (Nat.sub 1 fp))) fuel

-- q=1 vb=1: delta=1 W0=1, d = m+1 with m odd -> d even -> p0 = 0, q = (d-1)%2 = 1
theorem t : seg 32 31 1 1 0 4096 0 1 0 = true := by decide +kernel
theorem t2 : seg 32 31 1 1 0 4095 0 1 0 = false := by decide +kernel
theorem t3 : seg 32 31 1 5 1 65536 0 5 1 = true := by decide +kernel

end CalibF
