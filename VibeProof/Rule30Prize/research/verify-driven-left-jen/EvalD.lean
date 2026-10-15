import Ruliology.CellularAutomata.Rule30Jen
namespace VerifyDrivenLeftJen
open Ruliology.CellularAutomata.Rule30Jen
def D (x : Int → Bool) (c : Nat → Bool) : Nat → Int → Bool
  | 0, p => if p < 0 then x p else if p = 0 then c 0 else false
  | t + 1, p => if p < 0 then rule (D x c t (p - 1)) (D x c t p) (D x c t (p + 1))
      else if p = 0 then c (t + 1) else false
def drv (w : List Bool) : Nat → Bool := fun t => if t = 0 then true else w.getD ((t - 1) % w.length) false
def colStr (w : List Bool) (m : Int) (n : Nat) : String :=
  String.join ((List.range n).map fun t => if D (fun _ => false) (drv w) t m then "1" else "0")
#eval colStr [false, true] (-1) 12
#eval colStr [false, false, true] (-1) 12
#eval colStr [false, true, true, true] (-2) 12
#eval colStr [true, true, false, true, false, false, false] (-3) 12
end VerifyDrivenLeftJen
