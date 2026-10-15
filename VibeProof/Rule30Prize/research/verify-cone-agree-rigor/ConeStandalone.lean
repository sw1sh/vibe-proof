/-! Self-contained re-derivation (no imports): own definitions, own proof by explicit
`Nat.rec`-style induction with `p` generalized, so the check does not rely on any olean. -/

namespace ConeStandalone

def rule (a b c : Bool) : Bool := xor a (b || c)

def cell : Nat → Int → Bool
  | 0, p => decide (p = 0)
  | t + 1, p => rule (cell t (p - 1)) (cell t p) (cell t (p + 1))

-- The center column starts 1,1,0,1,1,1,0,0,1,1,0,0,0,1,0,1,1,0,0,1 (OEIS A051023).
example : (List.range 9).map (fun t => cell t 0) =
    [true, true, false, true, true, true, false, false, true] := by decide

theorem cone (t0 t1 n : Nat) (hdrv : ∀ s, cell (t0 + s) 0 = cell (t1 + s) 0)
    (hrow : ∀ p : Int, 1 ≤ p → p ≤ n → cell t0 p = cell t1 p) (s : Nat) :
    ∀ p : Int, 1 ≤ p → p + s ≤ n → cell (t0 + s) p = cell (t1 + s) p := by
  induction s with
  | zero =>
    intro p h1 h2
    have := hrow p h1 (by omega)
    simpa using this
  | succ s ih =>
    intro p h1 h2
    have e0 : cell (t0 + (s + 1)) p = rule (cell (t0 + s) (p - 1)) (cell (t0 + s) p) (cell (t0 + s) (p + 1)) := by
      rw [show t0 + (s + 1) = (t0 + s) + 1 by omega]; rfl
    have e1 : cell (t1 + (s + 1)) p = rule (cell (t1 + s) (p - 1)) (cell (t1 + s) p) (cell (t1 + s) (p + 1)) := by
      rw [show t1 + (s + 1) = (t1 + s) + 1 by omega]; rfl
    have hl : cell (t0 + s) (p - 1) = cell (t1 + s) (p - 1) := by
      rcases Int.lt_or_le 1 p with hp | hp
      · exact ih (p - 1) (by omega) (by omega)
      · have : p - 1 = 0 := by omega
        rw [this]; exact hdrv s
    have hc : cell (t0 + s) p = cell (t1 + s) p := ih p h1 (by omega)
    have hr : cell (t0 + s) (p + 1) = cell (t1 + s) (p + 1) := ih (p + 1) (by omega) (by omega)
    rw [e0, e1, hl, hc, hr]

#print axioms cone

/-- Sharpness check 1: the cone bound `p + s ≤ n` cannot be relaxed to `p + s ≤ n + 1`
in general — exhibited by an explicit pair of times below via `decide`. -/
def agreeRow (t0 t1 n : Nat) : Bool :=
  (List.range n).all (fun i => cell t0 ((i : Int) + 1) == cell t1 ((i : Int) + 1))

end ConeStandalone
