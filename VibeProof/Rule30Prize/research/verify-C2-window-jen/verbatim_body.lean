namespace Rule30JenWindow

open Rule30Jen

/-- `column i || column (i + 1)`: the only information about column `i + 1` that the left-permutive
reconstruction from columns `i`, `i + 1` uses. -/
def orCol (i : Int) (t : Nat) : Bool := cell t i || cell t (i + 1)

/-! ### Reconstruction to the left from a column and its `orCol` -/

theorem cell_left' (t : Nat) (i : Int) : cell t (i - 1) = xor (cell (t + 1) i) (orCol i t) :=
  cell_left t i

/-- **Determination lemma.** If column `i` agrees at times `t₁ + s`, `t₂ + s` for `s ≤ m`, and
`orCol i` agrees for `s < m`, then column `i - k` agrees for `s + k ≤ m`. -/
theorem determine {t₁ t₂ : Nat} {i : Int} (m : Nat)
    (hc : ∀ s, s ≤ m → cell (t₁ + s) i = cell (t₂ + s) i)
    (he : ∀ s, s < m → orCol i (t₁ + s) = orCol i (t₂ + s)) :
    ∀ k s, s + k ≤ m → cell (t₁ + s) (i - k) = cell (t₂ + s) (i - k) ∧
      (s + k < m → orCol (i - k) (t₁ + s) = orCol (i - k) (t₂ + s)) := by
  intro k
  induction k with
  | zero =>
    intro s hs
    rw [show i - ((0 : Nat) : Int) = i by omega]
    exact ⟨hc s (by omega), fun h => he s (by omega)⟩
  | succ k ih =>
    intro s hs
    have hA : cell (t₁ + s) (i - ((k + 1 : Nat) : Int)) = cell (t₂ + s) (i - ((k + 1 : Nat) : Int)) := by
      have e : i - ((k + 1 : Nat) : Int) = (i - (k : Int)) - 1 := by omega
      rw [e, cell_left', cell_left', show t₁ + s + 1 = t₁ + (s + 1) by omega,
        show t₂ + s + 1 = t₂ + (s + 1) by omega, (ih (s + 1) (by omega)).1,
        (ih s (by omega)).2 (by omega)]
    refine ⟨hA, fun h => ?_⟩
    have hB := (ih s (by omega)).1
    unfold orCol
    rw [hA, show i - ((k + 1 : Nat) : Int) + 1 = i - (k : Int) by omega, hB]

/-- **Window form of Jen's theorem.** No periodicity is assumed: two times `t₁ < t₂` never carry
the same (center column, `orCol 0`) window of length `t₂`. -/
theorem window_jen {t₁ t₂ : Nat} (h : t₁ < t₂)
    (hc : ∀ s, s ≤ t₂ → cell (t₁ + s) 0 = cell (t₂ + s) 0)
    (he : ∀ s, s < t₂ → orCol 0 (t₁ + s) = orCol 0 (t₂ + s)) : False := by
  have key := (determine (i := 0) t₂ hc he t₂ 0 (by omega)).1
  simp only [Nat.add_zero, Int.zero_sub] at key
  rw [cell_eq_false_of_lt t₁ (-(t₂ : Int)) (by omega), cell_left_edge t₂] at key
  exact absurd key (by decide)

/-- The same for any column `i`: two times `t₁ < t₂` never carry the same (column `i`, `orCol i`)
window of length `m` when `i - m = -t₂`. -/
theorem window_jen_col {t₁ t₂ : Nat} {i : Int} (m : Nat) (h : t₁ < t₂) (hm : i - (m : Int) = -(t₂ : Int))
    (hc : ∀ s, s ≤ m → cell (t₁ + s) i = cell (t₂ + s) i)
    (he : ∀ s, s < m → orCol i (t₁ + s) = orCol i (t₂ + s)) : False := by
  have key := (determine m hc he m 0 (by omega)).1
  simp only [Nat.add_zero] at key
  rw [hm, cell_eq_false_of_lt t₁ (-(t₂ : Int)) (by omega), cell_left_edge t₂] at key
  exact absurd key (by decide)
