namespace Calib4

noncomputable def scanN : Nat → List Nat → List Nat → List Nat × Nat := fun acc as =>
  List.rec (motive := fun _ => Nat → List Nat → List Nat × Nat)
    (fun acc _ => ([], acc))
    (fun a _ ih acc bs =>
      let v := Nat.xor acc (Nat.lor a (List.headD bs 0))
      let r := ih v (List.tail bs)
      (v :: r.1, r.2))
    as acc

noncomputable def mapX (t : Nat) : List Nat → List Nat :=
  List.rec (motive := fun _ => List Nat) [] (fun a _ ih => Nat.xor t a :: ih)

def dbl : Nat → Nat → Nat → Nat
  | 0, B, _ => B
  | m + 1, B, len => dbl m (Nat.lor B (Nat.shiftLeft B len)) (Nat.add len len)

def pat (n s : Nat) : Nat :=
  dbl (n - (s + 1)) (Nat.shiftLeft (Nat.sub (Nat.pow 2 (Nat.pow 2 s)) 1) (Nat.pow 2 s)) (Nat.pow 2 (s + 1))

def yFree (n c ALL : Nat) (pats : List Nat) (s : Nat) : Nat :=
  if s < n then pats.getD s 0 else if c.testBit (s - n) then ALL else 0

noncomputable def stepR (W n c ALL : Nat) (pats : List Nat) (k : Nat) (R Rm : List Nat) : List Nat × Nat :=
  Bool.rec
    (Bool.rec
      (let r := scanN 0 R (0 :: Rm); (r.2 :: mapX r.2 r.1, r.2))
      (let y := yFree n c ALL pats (Nat.div k 2); let r := scanN y R (0 :: Rm); (y :: r.1, r.2))
      (Nat.ble (Nat.add k 1) W))
    (let r := scanN ALL R (0 :: Rm); (ALL :: r.1, r.2))
    (Nat.beq (Nat.mod k 2) 0)

noncomputable def band (a b : Bool) : Bool := Bool.rec false b a

noncomputable def run (W n c ALL : Nat) (pats : List Nat) (fuel : Nat) : Nat → List Nat → List Nat → Nat → Bool :=
  Nat.rec (motive := fun _ => Nat → List Nat → List Nat → Nat → Bool)
    (fun _ _ _ alive => Nat.beq alive 0)
    (fun _ ih k R Rm alive =>
      let st := stepR W n c ALL pats k R Rm
      ih (Nat.add k 1) st.1 R
        (Bool.rec alive (Nat.land alive (Nat.xor ALL st.2))
          (band (Nat.beq (Nat.mod k 2) 0) (Nat.blt W (Nat.add k 1)))))
    fuel

noncomputable def check (W K n c : Nat) : Bool :=
  let ALL := Nat.sub (Nat.pow 2 (Nat.pow 2 n)) 1
  run W n c ALL ((List.range n).map (pat n)) K 0 [] [] ALL

theorem t : check 40 76 20 0 = true := by decide +kernel

end Calib4
