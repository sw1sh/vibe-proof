import Ruliology.CellularAutomata.Rule30Prize

/-! Independent re-proof of claim C2 (window form of Jen), written from scratch.
`orCol` is spelled out as `cell t i || cell t (i + 1)` so nothing depends on the
generalize-jen file. Only `Rule30Jen.cell`, `cell_left`, `cell_eq_false_of_lt`,
`cell_left_edge` from the merged library are used. -/

namespace VerifyC2
open Ruliology.CellularAutomata.Rule30Jen

/-- Determination by induction on an upper bound `n` for the depth `k`. -/
theorem det_all {t1 t2 : Nat} {i : Int} (m : Nat)
    (hc : ∀ s, s ≤ m → cell (t1 + s) i = cell (t2 + s) i)
    (he : ∀ s, s < m → (cell (t1 + s) i || cell (t1 + s) (i + 1)) =
      (cell (t2 + s) i || cell (t2 + s) (i + 1))) :
    ∀ n, ∀ k, k ≤ n → ∀ s, s + k ≤ m → cell (t1 + s) (i - k) = cell (t2 + s) (i - k) := by
  intro n
  induction n with
  | zero =>
    intro k hk s hs
    have : k = 0 := by omega
    subst this
    have := hc s (by omega)
    simpa using this
  | succ n ih =>
    intro k hk s hs
    by_cases hkn : k ≤ n
    · exact ih k hkn s hs
    · have hk' : k = n + 1 := by omega
      subst hk'
      have e : i - ((n + 1 : Nat) : Int) = (i - (n : Int)) - 1 := by omega
      rw [e, cell_left (t1 + s), cell_left (t2 + s)]
      have h1 : cell (t1 + s + 1) (i - n) = cell (t2 + s + 1) (i - n) := by
        have := ih n (Nat.le_refl n) (s + 1) (by omega)
        rwa [show t1 + (s + 1) = t1 + s + 1 by omega,
          show t2 + (s + 1) = t2 + s + 1 by omega] at this
      have h2 : (cell (t1 + s) (i - n) || cell (t1 + s) (i - n + 1)) =
          (cell (t2 + s) (i - n) || cell (t2 + s) (i - n + 1)) := by
        cases n with
        | zero =>
          have := he s (by omega)
          simpa using this
        | succ n' =>
          have a := ih (n' + 1) (Nat.le_refl _) s (by omega)
          have b := ih n' (by omega) s (by omega)
          rw [show i - ((n' + 1 : Nat) : Int) + 1 = i - (n' : Int) by omega, a, b]
      rw [h1, h2]

/-- C2, general column form, exactly as worded in the claim
(column window `s ≤ m`, orCol window `s < m`, `i - m = -t2`). -/
theorem claim_general (t1 t2 : Nat) (i : Int) (m : Nat) (h : t1 < t2)
    (hm : i - (m : Int) = -(t2 : Int)) :
    ¬ ((∀ s, s ≤ m → cell (t1 + s) i = cell (t2 + s) i) ∧
       (∀ s, s < m → (cell (t1 + s) i || cell (t1 + s) (i + 1)) =
          (cell (t2 + s) i || cell (t2 + s) (i + 1)))) := by
  rintro ⟨hc, he⟩
  have key := det_all m hc he m m (Nat.le_refl m) 0 (by omega)
  rw [Nat.add_zero, Nat.add_zero, hm, cell_eq_false_of_lt t1 (-(t2 : Int)) (by omega),
    cell_left_edge t2] at key
  exact Bool.false_ne_true key

/-- C2, column 0 form, exactly as worded in the claim. -/
theorem claim_col0 (t1 t2 : Nat) (h : t1 < t2) :
    ¬ ((∀ s, s ≤ t2 → cell (t1 + s) 0 = cell (t2 + s) 0) ∧
       (∀ s, s < t2 → (cell (t1 + s) 0 || cell (t1 + s) 1) =
          (cell (t2 + s) 0 || cell (t2 + s) 1))) :=
  claim_general t1 t2 0 t2 h (by omega)

/-- Sanity: the premise `t1 < t2` with these hypotheses is about the real pattern; check the
light-cone facts on a concrete instance by evaluation. -/
example : cell 3 (-5) = false ∧ cell 5 (-5) = true := by decide

end VerifyC2

#print axioms VerifyC2.det_all
#print axioms VerifyC2.claim_general
#print axioms VerifyC2.claim_col0
