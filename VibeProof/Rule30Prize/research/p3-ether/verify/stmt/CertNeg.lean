import P3NoWall
import P3Trap001
open Ruliology.CellularAutomata Rule30EtherThree

-- (1) t001 with bit 0 of u set: label 0 (white phase) would need column 1 black. Must FAIL.
def t001u : PTrap := { t001 with u := t001_u + 1 }
theorem negU : t001u.check = true := by decide +kernel

-- (2) t001 with one strip bit flipped (bit 1000 of R, inside state 21). Must FAIL.
def t001r : PTrap := { t001 with R := t001_R ^^^ (2 ^ 1000) }
theorem negR : t001r.check = true := by decide +kernel

-- (3) t001 with modulus 42 instead of 21 (labels then do not wrap at 21). Must FAIL.
def t001m : PTrap := { t001 with m := 42 }
theorem negM : t001m.check = true := by decide +kernel

-- (4) no-wall certificate, column 0, with the distance of state (phase 0, r = 0) forced to 0. Must FAIL.
theorem negNW : nwCheck 0 12 (nwD (nw0_12_d0 - nw0_12_d0 % 32) nw0_12_d1 nw0_12_d2)
    (nwD nw0_12_z0 nw0_12_z1 nw0_12_z2) = true := by decide +kernel

-- (5) positive control: the unmodified t001 passes again here.
theorem pos : t001.check = true := by decide +kernel
#eval (nw0_12_d0 % 32, t001.st 21 % 2, t001.lab 21)
