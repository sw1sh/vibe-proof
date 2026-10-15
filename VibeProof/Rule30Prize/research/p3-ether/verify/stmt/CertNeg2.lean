import P3NoWall
import P3Trap001
open Ruliology.CellularAutomata Rule30EtherThree

def badR : Nat := t001_R ^^^ (2 ^ 1000)
def t001r : PTrap := { t001 with R := badR }
def negRprop : Prop := t001r.check = true
instance : Decidable negRprop := inferInstanceAs (Decidable (t001r.check = true))
theorem negR : negRprop := by decide +kernel

def badD : Nat := nw0_12_d0 - nw0_12_d0 % 32
def negNWprop : Prop := nwCheck 0 12 (nwD badD nw0_12_d1 nw0_12_d2) (nwD nw0_12_z0 nw0_12_z1 nw0_12_z2) = true
instance : Decidable negNWprop := inferInstanceAs (Decidable (nwCheck 0 12 (nwD badD nw0_12_d1 nw0_12_d2) (nwD nw0_12_z0 nw0_12_z1 nw0_12_z2) = true))
theorem negNW : negNWprop := by decide +kernel
#eval t001r.check
#eval nwCheck 0 12 (nwD badD nw0_12_d1 nw0_12_d2) (nwD nw0_12_z0 nw0_12_z1 nw0_12_z2)
