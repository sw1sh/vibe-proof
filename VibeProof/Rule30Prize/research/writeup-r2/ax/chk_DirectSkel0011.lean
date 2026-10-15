import Ruliology.CellularAutomata.Rule30Jen

/-! Independent re-proof of the 0011 skeleton following the hand proof (a)-(c), without certificates. -/

namespace VerifyB2
open Ruliology.CellularAutomata.Rule30Jen

theorem step1 (t : Nat) : cell (t + 1) 1 = xor (cell t 0) (cell t 1 || cell t 2) := rfl
theorem step2 (t : Nat) : cell (t + 1) 2 = xor (cell t 1) (cell t 2 || cell t 3) := rfl
theorem stepm1 (t : Nat) : cell t (-1) = xor (cell (t + 1) 0) (cell t 0 || cell t 1) := cell_left t 0

/-- Local backward step (a), as a statement about Booleans. -/
theorem local_step (A1 A2 B1 B2 C1 C2 C3 D1 D2 E1 : Bool)
    (hB1 : B1 = xor false (A1 || A2))
    (hC1 : C1 = xor true (B1 || B2))
    (hD1 : D1 = xor true (C1 || C2))
    (hD2 : D2 = xor C1 (C2 || C3))
    (hE1 : E1 = xor false (D1 || D2))
    (hE : E1 = false) : A1 = false ∧ B1 = false ∧ C1 = true ∧ D1 = false := by
  subst hB1 hC1 hD1 hD2 hE1
  revert hE
  cases A1 <;> cases A2 <;> cases B2 <;> cases C2 <;> cases C3 <;> decide

theorem skel (T : Nat) (h : ∀ t, T ≤ t → cell t 0 = decide (2 ≤ (t - T) % 4)) :
    ∃ T', T ≤ T' ∧ ∀ t, T' ≤ t →
      ((t - T) % 4 = 0 → cell t (-1) = cell t 1) ∧
      ((t - T) % 4 = 1 → cell t 1 = true ∧ cell t (-1) = false) ∧
      ((t - T) % 4 = 2 → cell t 1 = true ∧ cell t (-1) = false) ∧
      ((t - T) % 4 = 3 → cell t 1 = false ∧ cell t (-1) = true) := by
  -- center values on blocks s = T + 4k
  have hc0 : ∀ k, cell (T + 4 * k) 0 = false := by
    intro k
    rw [h _ (by omega), show (T + 4 * k - T) % 4 = 0 by omega]; rfl
  have hc1 : ∀ k, cell (T + 4 * k + 1) 0 = false := by
    intro k
    rw [h _ (by omega), show (T + 4 * k + 1 - T) % 4 = 1 by omega]; rfl
  have hc2 : ∀ k, cell (T + 4 * k + 2) 0 = true := by
    intro k
    rw [h _ (by omega), show (T + 4 * k + 2 - T) % 4 = 2 by omega]; rfl
  have hc3 : ∀ k, cell (T + 4 * k + 3) 0 = true := by
    intro k
    rw [h _ (by omega), show (T + 4 * k + 3 - T) % 4 = 3 by omega]; rfl
  have hc4 : ∀ k, cell (T + 4 * k + 4) 0 = false := by
    intro k
    have := hc0 (k + 1)
    rw [show T + 4 * (k + 1) = T + 4 * k + 4 by omega] at this
    exact this
  -- (a) backward step, with the extra values on the earlier block
  have back : ∀ k, cell (T + 4 * k + 5) 1 = false →
      cell (T + 4 * k + 1) 1 = false ∧ cell (T + 4 * k + 2) 1 = false ∧
      cell (T + 4 * k + 3) 1 = true ∧ cell (T + 4 * k + 4) 1 = false := by
    intro k hE
    have eB1 := step1 (T + 4 * k + 1)
    have eC1 := step1 (T + 4 * k + 2)
    have eD1 := step1 (T + 4 * k + 3)
    have eD2 := step2 (T + 4 * k + 3)
    have eE1 := step1 (T + 4 * k + 4)
    rw [hc1 k] at eB1
    rw [hc2 k] at eC1
    rw [hc3 k] at eD1
    rw [hc4 k] at eE1
    exact local_step _ _ _ _ _ _ _ _ _ _ eB1 eC1 eD1 eD2 eE1 hE
  -- downward closure
  have down : ∀ n k, cell (T + 4 * (k + n) + 1) 1 = false → cell (T + 4 * k + 1) 1 = false := by
    intro n
    induction n with
    | zero => intro k hk; simpa using hk
    | succ n ih =>
      intro k hk
      have h1 : cell (T + 4 * (k + n) + 1) 1 = false := by
        have := (back (k + n) (by rw [show T + 4 * (k + n) + 5 = T + 4 * (k + (n + 1)) + 1 by omega]; exact hk)).1
        exact this
      exact ih k h1
  by_cases hall : ∀ k, cell (T + 4 * k + 1) 1 = false
  · -- (b) column 1 is eventually periodic: contradiction with Jen
    exfalso
    have col1 : ∀ t, T + 1 ≤ t → cell t 1 = decide ((t - T) % 4 = 3) := by
      intro t ht
      obtain ⟨k, j, hj, rfl⟩ : ∃ k j, j < 4 ∧ t = T + 4 * k + j + 1 :=
        ⟨(t - T - 1) / 4, (t - T - 1) % 4, Nat.mod_lt _ (by decide), by omega⟩
      have hb := back k (by rw [show T + 4 * k + 5 = T + 4 * (k + 1) + 1 by omega]; exact hall (k + 1))
      have hj' : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
      rcases hj' with rfl | rfl | rfl | rfl
      · rw [show (T + 4 * k + 0 + 1 - T) % 4 = 1 by omega]; exact hb.1
      · rw [show (T + 4 * k + 1 + 1 - T) % 4 = 2 by omega]; exact hb.2.1
      · rw [show (T + 4 * k + 2 + 1 - T) % 4 = 3 by omega]; exact hb.2.2.1
      · rw [show (T + 4 * k + 3 + 1 - T) % 4 = 0 by omega]; exact hb.2.2.2
    have p0 : EventuallyPeriodic fun t => cell t 0 := by
      refine ⟨T, 4, by decide, fun t ht => ?_⟩
      show cell (t + 4) 0 = cell t 0
      rw [h (t + 4) (by omega), h t ht, show (t + 4 - T) % 4 = (t - T) % 4 by omega]
    have p1 : EventuallyPeriodic fun t => cell t (0 + 1) := by
      refine ⟨T + 1, 4, by decide, fun t ht => ?_⟩
      show cell (t + 4) 1 = cell t 1
      rw [col1 (t + 4) (by omega), col1 t ht, show (t + 4 - T) % 4 = (t - T) % 4 by omega]
    exact not_adjacent 0 p0 p1
  · -- (c) eventually column 1 is black at phase 1
    have : ∃ K, cell (T + 4 * K + 1) 1 = true := by
      refine Classical.byContradiction fun hn => hall fun k => ?_
      cases hk : cell (T + 4 * k + 1) 1 with
      | false => rfl
      | true => exact absurd ⟨k, hk⟩ hn
    obtain ⟨K, hK⟩ := this
    have late : ∀ k, K ≤ k → cell (T + 4 * k + 1) 1 = true := by
      intro k hk
      cases hv : cell (T + 4 * k + 1) 1 with
      | true => rfl
      | false =>
        have := down (k - K) K (by rw [show K + (k - K) = k by omega]; exact hv)
        rw [hK] at this; exact absurd this (by decide)
    refine ⟨T + 4 * K, by omega, fun t ht => ?_⟩
    obtain ⟨k, j, hj, hkK, rfl⟩ : ∃ k j, j < 4 ∧ K ≤ k ∧ t = T + 4 * k + j :=
      ⟨(t - T) / 4, (t - T) % 4, Nat.mod_lt _ (by decide), by omega, by omega⟩
    have hph : (T + 4 * k + j - T) % 4 = j := by omega
    rw [hph]
    have v1 := late k hkK
    have v2 : cell (T + 4 * k + 2) 1 = true := by
      rw [step1 (T + 4 * k + 1), hc1 k, v1]; rfl
    have v3 : cell (T + 4 * k + 3) 1 = false := by
      rw [step1 (T + 4 * k + 2), hc2 k, v2]; rfl
    have hj' : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
    rcases hj' with rfl | rfl | rfl | rfl
    · refine ⟨fun _ => ?_, fun h => absurd h (by decide), fun h => absurd h (by decide),
        fun h => absurd h (by decide)⟩
      rw [stepm1, show T + 4 * k + 0 + 1 = T + 4 * k + 1 by omega, hc1 k,
        show T + 4 * k + 0 = T + 4 * k by omega, hc0 k]
      cases cell (T + 4 * k) 1 <;> rfl
    · refine ⟨fun h => absurd h (by decide), fun _ => ⟨v1, ?_⟩, fun h => absurd h (by decide),
        fun h => absurd h (by decide)⟩
      rw [stepm1, show T + 4 * k + 1 + 1 = T + 4 * k + 2 by omega, hc2 k, hc1 k, v1]; rfl
    · refine ⟨fun h => absurd h (by decide), fun h => absurd h (by decide), fun _ => ⟨v2, ?_⟩,
        fun h => absurd h (by decide)⟩
      rw [stepm1, show T + 4 * k + 2 + 1 = T + 4 * k + 3 by omega, hc3 k, hc2 k]; rfl
    · refine ⟨fun h => absurd h (by decide), fun h => absurd h (by decide), fun h => absurd h (by decide),
        fun _ => ⟨v3, ?_⟩⟩
      rw [stepm1, show T + 4 * k + 3 + 1 = T + 4 * k + 4 by omega, hc4 k, hc3 k]; rfl

end VerifyB2

#print axioms VerifyB2.skel

-- the imported `cell` is rule 30 from a single black cell: center column starts 1,1,0,1,1,1,0,0,1,1,0,0,0
#eval (List.range 13).map fun t => if Ruliology.CellularAutomata.Rule30Jen.cell t 0 then 1 else 0

-- writeup-r2 axiom audit (appended)
#print axioms VerifyB2.skel
