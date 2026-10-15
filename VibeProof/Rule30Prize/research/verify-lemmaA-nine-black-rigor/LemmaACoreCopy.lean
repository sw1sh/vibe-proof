/-! Finite core of Lemma A ("nine blacks shield"), checked with Nat bit operations.
A row is a Nat whose bit `i` is the cell at column m+1+i; the left boundary (column m) is black.
One step: new = ((row <<< 1) ||| 1) ^^^ (row ||| (row >>> 1)) (rule 30, left boundary 1).
After 9 steps, bits 0 and 1 lie in the light cone of the 11 initial bits, and they are 0 and 1. -/

def stepB (row : Nat) : Nat := ((row <<< 1) ||| 1) ^^^ (row ||| (row >>> 1))

def runB : Nat → Nat → Nat
  | 0, row => row
  | k + 1, row => runB k (stepB row)

/-- check all rows `n` with `lo ≤ n < lo + len`. -/
def checkRange (k bits target lo : Nat) : Nat → Bool
  | 0 => true
  | len + 1 => (runB k (lo + len) % 2 ^ bits == target) && checkRange k bits target lo len

-- 9 black steps force (column m+1, column m+2) = (white, black): low two bits = 0b10 = 2.
theorem lemmaA_core_0 : checkRange 9 2 2 0 512 = true := by decide +kernel
theorem lemmaA_core_1 : checkRange 9 2 2 512 512 = true := by decide +kernel
theorem lemmaA_core_2 : checkRange 9 2 2 1024 512 = true := by decide +kernel
theorem lemmaA_core_3 : checkRange 9 2 2 1536 512 = true := by decide +kernel

-- 8 black steps do not force column m+1: some 10-bit row gives bit 0 = 1.
theorem eight_not_enough : checkRange 8 1 0 0 1024 = false := by decide +kernel

#print axioms lemmaA_core_0
#print axioms lemmaA_core_3
#print axioms eight_not_enough
