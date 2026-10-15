-- Kernel check of the non-sufficiency witnesses for the local (free right-half) system,
-- using the same `stepRow`/`runBlack` as AbsorbRight.lean (copied; rule = l xor (c || r)).
def rule (a b c : Bool) : Bool := xor a (b || c)
def stepRow (l : Bool) : List Bool → List Bool
  | a :: b :: rest => rule l a b :: stepRow a (b :: rest)
  | _ => []
def runBlack : Nat → List Bool → List Bool
  | 0, L => L
  | k + 1, L => runBlack k (stepRow true L)
def bitsList (x W : Nat) : List Bool := (List.range W).map (fun i => x.testBit i)
-- j = 1: 8 black steps, row of 10 cells -> cells m+1, m+2 = (1, 0), not (0, 1)
theorem w1 : runBlack 8 (bitsList 0x13 10) = [true, false] := by decide +kernel
-- j = 2: 17 black steps, row of 21 cells -> 0110, not 0101
theorem w2 : runBlack 17 (bitsList 0x45 21) = [false, true, true, false] := by decide +kernel
-- j = 3: 26 black steps, row of 32 cells -> 010110, not 010101
theorem w3 : runBlack 26 (bitsList 0xe6f1b2f3 32) = [false, true, false, true, true, false] := by decide +kernel
#print axioms w3
