namespace Calib

/-- xor-scan: after `r` rounds, bit `j` is the xor of bits `j .. j + 2^r - 1`. -/
def scanR : Nat → Nat → Nat
  | 0, g => g
  | r + 1, g => scanR r g ^^^ (scanR r g >>> 2 ^ r)

def step (k A B : Nat) (b : Bool) : Nat :=
  let m := 2 ^ k - 1
  let s := scanR 7 ((A ||| B) &&& m)
  if b then ((s ^^^ m) &&& m) ||| 2 ^ k else s &&& m

def dfs (W pre plen : Nat) : Nat → Nat → Nat → Nat → Bool
  | 0, _, _, _ => false
  | n + 1, k, A, B =>
    let go : Bool → Bool := fun b =>
      (decide (W < k + 1) && step k A B b % 2 == 1) || dfs W pre plen n (k + 1) B (step k A B b)
    if k % 2 = 0 then go true
    else if k / 2 < plen then go (pre.testBit (k / 2))
    else go false && go true

theorem c26 : dfs 26 0 0 46 0 0 0 = true := by decide +kernel

end Calib
