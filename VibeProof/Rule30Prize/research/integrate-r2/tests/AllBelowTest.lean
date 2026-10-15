import Ruliology.CellularAutomata.Rule30ZeroBoundaryStripe
import Ruliology.CellularAutomata.Rule30StripCertificates
open Ruliology.CellularAutomata Rule30ZeroBoundaryStripe
theorem front_check2' : Rule30StripCertificates.allBelow (fun v => v % 2 == 1 || frontWithin 13 9 v) (2 ^ 14) = true := by
  decide +kernel
