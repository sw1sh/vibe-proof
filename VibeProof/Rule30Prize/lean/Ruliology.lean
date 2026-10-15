import Ruliology.CellularAutomata.Rule30Predecessors
import Ruliology.CellularAutomata.Rule30PredecessorCounts
import Ruliology.CellularAutomata.Rule30Blocks
import Ruliology.CellularAutomata.Rule30Jen
import Ruliology.CellularAutomata.Rule30Prize
import Ruliology.CellularAutomata.Rule30Window
import Ruliology.CellularAutomata.Rule30MaskedJen
import Ruliology.CellularAutomata.Rule30BlackRuns
import Ruliology.CellularAutomata.Rule30BlackRunBlocks
import Ruliology.CellularAutomata.Rule30StripCertificates
import Ruliology.CellularAutomata.Rule30StripCertificateTable
import Ruliology.CellularAutomata.Rule30DrivenLeft
import Ruliology.CellularAutomata.Rule30RightPeriods
import Ruliology.CellularAutomata.Rule30WhiteSeed
import Ruliology.CellularAutomata.Rule30Realization
import Ruliology.CellularAutomata.Rule30FactorWindow
import Ruliology.CellularAutomata.Rule30PeriodTwo
import Ruliology.CellularAutomata.Rule30ZeroBoundary
import Ruliology.CellularAutomata.Rule30ZeroBoundaryStripe
import Ruliology.CellularAutomata.Rule30ZeroBoundarySmall
import Ruliology.CellularAutomata.Rule30ZeroBoundaryBarriers
import Ruliology.CellularAutomata.Rule30Ether
import Ruliology.CellularAutomata.Rule30PeriodTwoCoupled
import Ruliology.CellularAutomata.Rule30PeriodFourSkeleton
import Ruliology.CellularAutomata.Rule30Diagonals
import Ruliology.CellularAutomata.Rule30ZeroBoundaryLanes
import Ruliology.CellularAutomata.Rule30ZeroBoundaryWidth52
import Ruliology.CellularAutomata.Rule30ZeroBoundaryStripeFront
import Ruliology.CellularAutomata.Rule30ZeroBoundaryStripeFamily
import Ruliology.CellularAutomata.Rule30EtherTrap
import Ruliology.CellularAutomata.Rule30EtherTrapWidth20
import Ruliology.CellularAutomata.Rule30PeriodTwoLanguage
import Ruliology.CellularAutomata.Rule30PeriodTwoWidth5
import Ruliology.CellularAutomata.Rule30PeriodTwoWidth6
import Ruliology.CellularAutomata.Rule30EtherThree
import Ruliology.CellularAutomata.Rule30EtherThreeNoWall
import Ruliology.CellularAutomata.Rule30EtherThreeTrap
import Ruliology.CellularAutomata.Rule30EtherThreeReach
import Ruliology.CellularAutomata.Rule30EtherThreeLeft
import Ruliology.CellularAutomata.Rule30EtherThreeSkeleton

/-!
# Rule 30 Prize: Lean snapshot

This is a snapshot of the `ruliology-lean` catalog taken on 2026-10-15.

It imports the catalog's 40 `Rule30*` modules, in the order of the catalog root. Their import
closure is 54 modules: these 40, the 13 data modules in `Rule30Certificates/`, and
`BusyBeaverLifetimes`, which `Rule30Blocks` imports. All 54 are copied byte for byte from the
catalog, and `SHA256SUMS` holds their SHA-256 hashes. This root file is the only new Lean file.

Core Lean 4.30.0, no dependencies. `README.md` maps the modules, names the headline theorems and
says how to build.
-/
