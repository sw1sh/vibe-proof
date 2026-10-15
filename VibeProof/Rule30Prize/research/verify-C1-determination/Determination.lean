import Ruliology.CellularAutomata.Rule30Jen

/-!
Adversarial check of claim C1 (determination lemma), against the project's own `cell`.
-/

namespace VerifyC1
open Ruliology.CellularAutomata.Rule30Jen

/-- `orCol i t = cell t i || cell t (i+1)`. -/
def orCol (i : Int) (t : Nat) : Bool := cell t i || cell t (i + 1)

/-- The claim, with the induction invariant (A_k, B_k) proved jointly over all `s`. -/
theorem determination_strong (i : Int) (t₁ t₂ m : Nat)
    (hA : ∀ s, s ≤ m → cell (t₁ + s) i = cell (t₂ + s) i)
    (hB : ∀ s, s < m → orCol i (t₁ + s) = orCol i (t₂ + s)) :
    ∀ k : Nat,
      (∀ s, s + k ≤ m → cell (t₁ + s) (i - k) = cell (t₂ + s) (i - k)) ∧
      (∀ s, s + k < m → orCol (i - k) (t₁ + s) = orCol (i - k) (t₂ + s)) := by
  intro k
  induction k with
  | zero =>
    refine ⟨fun s hs => ?_, fun s hs => ?_⟩
    · simpa using hA s (by omega)
    · simpa using hB s (by omega)
  | succ k ih =>
    obtain ⟨ihA, ihB⟩ := ih
    -- A_{k+1}(s) from left-permutivity at column i-k, using A_k(s+1) and B_k(s)
    have hA' : ∀ s, s + (k + 1) ≤ m →
        cell (t₁ + s) (i - ((k + 1 : Nat) : Int)) = cell (t₂ + s) (i - ((k + 1 : Nat) : Int)) := by
      intro s hs
      have e : i - ((k + 1 : Nat) : Int) = (i - (k : Int)) - 1 := by omega
      have h1 := ihA (s + 1) (by omega)
      have h2 := ihB s (by omega)
      simp only [orCol] at h2
      rw [e, cell_left (t₁ + s) (i - (k : Int)), cell_left (t₂ + s) (i - (k : Int)), h2,
        show t₁ + s + 1 = t₁ + (s + 1) by omega, show t₂ + s + 1 = t₂ + (s + 1) by omega, h1]
    refine ⟨hA', ?_⟩
    -- B_{k+1}(s) from A_{k+1}(s) and A_k(s)
    intro s hs
    simp only [orCol]
    rw [hA' s (by omega), show i - ((k + 1 : Nat) : Int) + 1 = i - (k : Int) by omega,
      ihA s (by omega)]

/-- **Claim C1** exactly as stated. -/
theorem determination (i : Int) (t₁ t₂ m : Nat)
    (hA : ∀ s, s ≤ m → cell (t₁ + s) i = cell (t₂ + s) i)
    (hB : ∀ s, s < m → orCol i (t₁ + s) = orCol i (t₂ + s)) :
    ∀ k s : Nat, s + k ≤ m → cell (t₁ + s) (i - k) = cell (t₂ + s) (i - k) :=
  fun k s hs => (determination_strong i t₁ t₂ m hA hB k).1 s hs

/-- Corollary: `cell t (i - m)` is a function of (column `i` on `[t, t+m]`, `orCol i` on
`[t, t+m)`): there is a single `F` (depending on `i, m`) with `cell t (i-m) = F (windows at t)`
for every `t`. -/
theorem determination_function (i : Int) (m : Nat) :
    ∃ F : (Nat → Bool) → (Nat → Bool) → Bool, ∀ t : Nat,
      cell t (i - m) =
        F (fun s => if s ≤ m then cell (t + s) i else false)
          (fun s => if s < m then orCol i (t + s) else false) := by
  classical
  let W : Nat → (Nat → Bool) × (Nat → Bool) := fun t =>
    ((fun s => if s ≤ m then cell (t + s) i else false),
     (fun s => if s < m then orCol i (t + s) else false))
  refine ⟨fun a b => if h : ∃ t, W t = (a, b) then cell (Classical.choose h) (i - m) else false,
    fun t => ?_⟩
  have h : ∃ t', W t' = W t := ⟨t, rfl⟩
  simp only [show ((fun s => if s ≤ m then cell (t + s) i else false),
     (fun s => if s < m then orCol i (t + s) else false)) = W t from rfl]
  rw [dif_pos h]
  have hc := Classical.choose_spec h
  -- agreement of windows gives agreement of the target cell
  have hA : ∀ s, s ≤ m → cell (Classical.choose h + s) i = cell (t + s) i := by
    intro s hs
    have := congrFun (congrArg Prod.fst hc) s
    simpa [W, hs] using this
  have hB : ∀ s, s < m → orCol i (Classical.choose h + s) = orCol i (t + s) := by
    intro s hs
    have := congrFun (congrArg Prod.snd hc) s
    simpa [W, hs] using this
  have := determination i (Classical.choose h) t m hA hB m 0 (by omega)
  simpa using this.symm

/-- "Column i+1 enters only at times where column i is white": `orCol` agreement follows from
agreement of column `i` plus agreement of column `i+1` at white times of column `i`. -/
theorem orCol_agree (i : Int) (t₁ t₂ : Nat) (h0 : cell t₁ i = cell t₂ i)
    (h1 : cell t₁ i = false → cell t₁ (i + 1) = cell t₂ (i + 1)) :
    orCol i t₁ = orCol i t₂ := by
  simp only [orCol]
  cases hc : cell t₁ i
  · rw [← h0, hc, h1 hc]
  · rw [← h0, hc]; rfl

/-- And when column `i` is black, `orCol` does not depend on column `i+1` at all. -/
theorem orCol_of_black (i : Int) (t : Nat) (h : cell t i = true) : orCol i t = true := by
  simp [orCol, h]

/-- Combined form of the remark: column `i` on `[t,t+m]` and column `i+1` at the white times
of column `i` in `[t,t+m)` determine column `i-k` on the triangle `s + k ≤ m`. -/
theorem determination_white (i : Int) (t₁ t₂ m : Nat)
    (hA : ∀ s, s ≤ m → cell (t₁ + s) i = cell (t₂ + s) i)
    (hW : ∀ s, s < m → cell (t₁ + s) i = false → cell (t₁ + s) (i + 1) = cell (t₂ + s) (i + 1)) :
    ∀ k s : Nat, s + k ≤ m → cell (t₁ + s) (i - k) = cell (t₂ + s) (i - k) :=
  determination i t₁ t₂ m hA
    (fun s hs => orCol_agree i (t₁ + s) (t₂ + s) (hA s (by omega)) (hW s hs))

end VerifyC1

#print axioms VerifyC1.determination
#print axioms VerifyC1.determination_function
#print axioms VerifyC1.determination_white
