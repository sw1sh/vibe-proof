import Ruliology.CellularAutomata.Rule30Jen
open Ruliology.CellularAutomata.Rule30Jen
-- the imported `rule` is literally left xor (center || right)
example : rule = fun a b c => xor a (b || c) := rfl
-- and it is Wolfram rule 30: output on neighbourhood (l,c,r) is bit (4l+2c+r) of 30
example : ∀ l c r : Bool, rule l c r = ((30 / 2 ^ (4 * l.toNat + 2 * c.toNat + r.toNat)) % 2 == 1) := by
  decide
