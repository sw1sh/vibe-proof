import Ruliology.CellularAutomata.Rule30Prize
namespace AbsorbRightV
open Ruliology.CellularAutomata.Rule30Jen

-- verbatim copies of the definitions from AbsorbRight.lean
def stepRow (l : Bool) : List Bool → List Bool
  | a :: b :: rest => rule l a b :: stepRow a (b :: rest)
  | _ => []

def traceCol1 : List Bool → List Bool → List Bool
  | [], row => [row.headD false]
  | c :: cs, row => row.headD false :: traceCol1 cs (stepRow c row)

def wbPattern : Nat → List Bool
  | 0 => []
  | j + 1 => false :: true :: wbPattern j

def drv (u : List Bool) : List Bool := u ++ List.replicate 9 true

def Determined (u : List Bool) (j0 : Nat) : Bool :=
  (allLists (u.length + 10 - 2 * j0)).all fun tail =>
    traceCol1 (drv u) (wbPattern j0 ++ tail) ==
      traceCol1 (drv u) (wbPattern j0 ++ List.replicate (u.length + 10 - 2 * j0) false)

#eval (s!"0 1:" ++ toString (Determined [false] 1) ++ " 2:" ++ toString (Determined [false] 2))
#eval (s!"00 1:" ++ toString (Determined [false, false] 1) ++ " 2:" ++ toString (Determined [false, false] 2))
#eval (s!"000 1:" ++ toString (Determined [false, false, false] 1) ++ " 2:" ++ toString (Determined [false, false, false] 2))
#eval (s!"010 2:" ++ toString (Determined [false, true, false] 2) ++ " 3:" ++ toString (Determined [false, true, false] 3))
#eval (s!"0000 1:" ++ toString (Determined [false, false, false, false] 1) ++ " 2:" ++ toString (Determined [false, false, false, false] 2))
#eval (s!"0010 2:" ++ toString (Determined [false, false, true, false] 2) ++ " 3:" ++ toString (Determined [false, false, true, false] 3))
#eval (s!"0100 1:" ++ toString (Determined [false, true, false, false] 1) ++ " 2:" ++ toString (Determined [false, true, false, false] 2))
#eval (s!"0110 2:" ++ toString (Determined [false, true, true, false] 2) ++ " 3:" ++ toString (Determined [false, true, true, false] 3))
#eval (s!"00000 2:" ++ toString (Determined [false, false, false, false, false] 2) ++ " 3:" ++ toString (Determined [false, false, false, false, false] 3))
#eval (s!"00010 2:" ++ toString (Determined [false, false, false, true, false] 2) ++ " 3:" ++ toString (Determined [false, false, false, true, false] 3))
#eval (s!"00100 2:" ++ toString (Determined [false, false, true, false, false] 2) ++ " 3:" ++ toString (Determined [false, false, true, false, false] 3))
#eval (s!"00110 2:" ++ toString (Determined [false, false, true, true, false] 2) ++ " 3:" ++ toString (Determined [false, false, true, true, false] 3))
#eval (s!"01000 2:" ++ toString (Determined [false, true, false, false, false] 2) ++ " 3:" ++ toString (Determined [false, true, false, false, false] 3))
#eval (s!"01010 1:" ++ toString (Determined [false, true, false, true, false] 1) ++ " 2:" ++ toString (Determined [false, true, false, true, false] 2))
#eval (s!"01100 1:" ++ toString (Determined [false, true, true, false, false] 1) ++ " 2:" ++ toString (Determined [false, true, true, false, false] 2))
#eval (s!"01110 1:" ++ toString (Determined [false, true, true, true, false] 1) ++ " 2:" ++ toString (Determined [false, true, true, true, false] 2))
#eval (s!"000000 2:" ++ toString (Determined [false, false, false, false, false, false] 2) ++ " 3:" ++ toString (Determined [false, false, false, false, false, false] 3))
#eval (s!"000010 2:" ++ toString (Determined [false, false, false, false, true, false] 2) ++ " 3:" ++ toString (Determined [false, false, false, false, true, false] 3))
#eval (s!"000100 2:" ++ toString (Determined [false, false, false, true, false, false] 2) ++ " 3:" ++ toString (Determined [false, false, false, true, false, false] 3))
#eval (s!"000110 2:" ++ toString (Determined [false, false, false, true, true, false] 2) ++ " 3:" ++ toString (Determined [false, false, false, true, true, false] 3))
#eval (s!"001000 2:" ++ toString (Determined [false, false, true, false, false, false] 2) ++ " 3:" ++ toString (Determined [false, false, true, false, false, false] 3))
#eval (s!"001010 1:" ++ toString (Determined [false, false, true, false, true, false] 1) ++ " 2:" ++ toString (Determined [false, false, true, false, true, false] 2))
#eval (s!"001100 1:" ++ toString (Determined [false, false, true, true, false, false] 1) ++ " 2:" ++ toString (Determined [false, false, true, true, false, false] 2))
#eval (s!"001110 2:" ++ toString (Determined [false, false, true, true, true, false] 2) ++ " 3:" ++ toString (Determined [false, false, true, true, true, false] 3))
#eval (s!"010000 2:" ++ toString (Determined [false, true, false, false, false, false] 2) ++ " 3:" ++ toString (Determined [false, true, false, false, false, false] 3))
#eval (s!"010010 2:" ++ toString (Determined [false, true, false, false, true, false] 2) ++ " 3:" ++ toString (Determined [false, true, false, false, true, false] 3))
#eval (s!"010100 2:" ++ toString (Determined [false, true, false, true, false, false] 2) ++ " 3:" ++ toString (Determined [false, true, false, true, false, false] 3))
#eval (s!"010110 2:" ++ toString (Determined [false, true, false, true, true, false] 2) ++ " 3:" ++ toString (Determined [false, true, false, true, true, false] 3))
#eval (s!"011000 3:" ++ toString (Determined [false, true, true, false, false, false] 3) ++ " 4:" ++ toString (Determined [false, true, true, false, false, false] 4))
#eval (s!"011010 1:" ++ toString (Determined [false, true, true, false, true, false] 1) ++ " 2:" ++ toString (Determined [false, true, true, false, true, false] 2))
#eval (s!"011100 2:" ++ toString (Determined [false, true, true, true, false, false] 2) ++ " 3:" ++ toString (Determined [false, true, true, true, false, false] 3))
#eval (s!"011110 1:" ++ toString (Determined [false, true, true, true, true, false] 1) ++ " 2:" ++ toString (Determined [false, true, true, true, true, false] 2))
#eval (s!"0000000 2:" ++ toString (Determined [false, false, false, false, false, false, false] 2) ++ " 3:" ++ toString (Determined [false, false, false, false, false, false, false] 3))
#eval (s!"0000010 2:" ++ toString (Determined [false, false, false, false, false, true, false] 2) ++ " 3:" ++ toString (Determined [false, false, false, false, false, true, false] 3))
#eval (s!"0000100 1:" ++ toString (Determined [false, false, false, false, true, false, false] 1) ++ " 2:" ++ toString (Determined [false, false, false, false, true, false, false] 2))
#eval (s!"0000110 2:" ++ toString (Determined [false, false, false, false, true, true, false] 2) ++ " 3:" ++ toString (Determined [false, false, false, false, true, true, false] 3))
#eval (s!"0001000 3:" ++ toString (Determined [false, false, false, true, false, false, false] 3) ++ " 4:" ++ toString (Determined [false, false, false, true, false, false, false] 4))
#eval (s!"0001010 2:" ++ toString (Determined [false, false, false, true, false, true, false] 2) ++ " 3:" ++ toString (Determined [false, false, false, true, false, true, false] 3))
#eval (s!"0001100 2:" ++ toString (Determined [false, false, false, true, true, false, false] 2) ++ " 3:" ++ toString (Determined [false, false, false, true, true, false, false] 3))
#eval (s!"0001110 2:" ++ toString (Determined [false, false, false, true, true, true, false] 2) ++ " 3:" ++ toString (Determined [false, false, false, true, true, true, false] 3))
#eval (s!"0010000 2:" ++ toString (Determined [false, false, true, false, false, false, false] 2) ++ " 3:" ++ toString (Determined [false, false, true, false, false, false, false] 3))
#eval (s!"0010010 1:" ++ toString (Determined [false, false, true, false, false, true, false] 1) ++ " 2:" ++ toString (Determined [false, false, true, false, false, true, false] 2))
#eval (s!"0010100 2:" ++ toString (Determined [false, false, true, false, true, false, false] 2) ++ " 3:" ++ toString (Determined [false, false, true, false, true, false, false] 3))
#eval (s!"0010110 1:" ++ toString (Determined [false, false, true, false, true, true, false] 1) ++ " 2:" ++ toString (Determined [false, false, true, false, true, true, false] 2))
#eval (s!"0011000 2:" ++ toString (Determined [false, false, true, true, false, false, false] 2) ++ " 3:" ++ toString (Determined [false, false, true, true, false, false, false] 3))
#eval (s!"0011010 2:" ++ toString (Determined [false, false, true, true, false, true, false] 2) ++ " 3:" ++ toString (Determined [false, false, true, true, false, true, false] 3))
#eval (s!"0011100 2:" ++ toString (Determined [false, false, true, true, true, false, false] 2) ++ " 3:" ++ toString (Determined [false, false, true, true, true, false, false] 3))
#eval (s!"0011110 2:" ++ toString (Determined [false, false, true, true, true, true, false] 2) ++ " 3:" ++ toString (Determined [false, false, true, true, true, true, false] 3))
#eval (s!"0100000 2:" ++ toString (Determined [false, true, false, false, false, false, false] 2) ++ " 3:" ++ toString (Determined [false, true, false, false, false, false, false] 3))
#eval (s!"0100010 2:" ++ toString (Determined [false, true, false, false, false, true, false] 2) ++ " 3:" ++ toString (Determined [false, true, false, false, false, true, false] 3))
#eval (s!"0100100 1:" ++ toString (Determined [false, true, false, false, true, false, false] 1) ++ " 2:" ++ toString (Determined [false, true, false, false, true, false, false] 2))
#eval (s!"0100110 2:" ++ toString (Determined [false, true, false, false, true, true, false] 2) ++ " 3:" ++ toString (Determined [false, true, false, false, true, true, false] 3))
#eval (s!"0101000 1:" ++ toString (Determined [false, true, false, true, false, false, false] 1) ++ " 2:" ++ toString (Determined [false, true, false, true, false, false, false] 2))
#eval (s!"0101010 2:" ++ toString (Determined [false, true, false, true, false, true, false] 2) ++ " 3:" ++ toString (Determined [false, true, false, true, false, true, false] 3))
#eval (s!"0101100 2:" ++ toString (Determined [false, true, false, true, true, false, false] 2) ++ " 3:" ++ toString (Determined [false, true, false, true, true, false, false] 3))
#eval (s!"0101110 2:" ++ toString (Determined [false, true, false, true, true, true, false] 2) ++ " 3:" ++ toString (Determined [false, true, false, true, true, true, false] 3))
#eval (s!"0110000 1:" ++ toString (Determined [false, true, true, false, false, false, false] 1) ++ " 2:" ++ toString (Determined [false, true, true, false, false, false, false] 2))
#eval (s!"0110010 1:" ++ toString (Determined [false, true, true, false, false, true, false] 1) ++ " 2:" ++ toString (Determined [false, true, true, false, false, true, false] 2))
#eval (s!"0110100 2:" ++ toString (Determined [false, true, true, false, true, false, false] 2) ++ " 3:" ++ toString (Determined [false, true, true, false, true, false, false] 3))
#eval (s!"0110110 1:" ++ toString (Determined [false, true, true, false, true, true, false] 1) ++ " 2:" ++ toString (Determined [false, true, true, false, true, true, false] 2))
#eval (s!"0111000 3:" ++ toString (Determined [false, true, true, true, false, false, false] 3) ++ " 4:" ++ toString (Determined [false, true, true, true, false, false, false] 4))
#eval (s!"0111010 2:" ++ toString (Determined [false, true, true, true, false, true, false] 2) ++ " 3:" ++ toString (Determined [false, true, true, true, false, true, false] 3))
#eval (s!"0111100 2:" ++ toString (Determined [false, true, true, true, true, false, false] 2) ++ " 3:" ++ toString (Determined [false, true, true, true, true, false, false] 3))
#eval (s!"0111110 2:" ++ toString (Determined [false, true, true, true, true, true, false] 2) ++ " 3:" ++ toString (Determined [false, true, true, true, true, true, false] 3))
end AbsorbRightV
