/-!
# The Mantovanelli–Hofstadter recursion

    Q̃(1) = Q̃(2) = 1,    Q̃(n) = Q̃(n − Q̃(n − 1)) + Q̃(n − Q̃(n − 2)) + (−1)ⁿ    (n ≥ 3)

This is OEIS A394051, introduced by Mantovanelli (arXiv:2603.16111). Cloitre (arXiv:2604.06237,
§§2–3) and Mantovanelli (arXiv:2603.29622) prove that it is well-defined: every recursive argument
is a positive integer smaller than the current index. This project machine-checks Cloitre's proof.

* `IsQTilde Q`: `Q` satisfies the recursion at every `n ≥ 3`, and both recursive arguments lie in
  `[1, n - 1]`.
* `isQTilde_unique`: such a `Q` is unique on the positive integers.
-/

namespace QTilde

/-- `(-1)^n`. -/
def sgn (n : Nat) : Int := if n % 2 = 0 then 1 else -1

/-- `Q` satisfies the parity-perturbed Hofstadter recursion, and every recursive argument is a
positive integer smaller than the current index. -/
def IsQTilde (Q : Nat → Int) : Prop :=
  Q 1 = 1 ∧ Q 2 = 1 ∧ ∀ n, 3 ≤ n → ∃ i j : Nat,
    1 ≤ i ∧ i < n ∧ 1 ≤ j ∧ j < n ∧
    (i : Int) = n - Q (n - 1) ∧ (j : Int) = n - Q (n - 2) ∧
    Q n = Q i + Q j + sgn n

/-- The recursion determines `Q` on the positive integers. -/
theorem isQTilde_unique {Q₁ Q₂ : Nat → Int} (h₁ : IsQTilde Q₁) (h₂ : IsQTilde Q₂) :
    ∀ n, 1 ≤ n → Q₁ n = Q₂ n := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro hn
    rcases (show n = 1 ∨ n = 2 ∨ 3 ≤ n by omega) with rfl | rfl | h3
    · rw [h₁.1, h₂.1]
    · rw [h₁.2.1, h₂.2.1]
    · obtain ⟨i₁, j₁, hi₁, hi₁', hj₁, hj₁', ei₁, ej₁, e₁⟩ := h₁.2.2 n h3
      obtain ⟨i₂, j₂, hi₂, hi₂', hj₂, hj₂', ei₂, ej₂, e₂⟩ := h₂.2.2 n h3
      have q1 := ih (n - 1) (by omega) (by omega)
      have q2 := ih (n - 2) (by omega) (by omega)
      have hi : i₁ = i₂ := by omega
      have hj : j₁ = j₂ := by omega
      subst hi hj
      rw [e₁, e₂, ih i₁ hi₁' hi₁, ih j₁ hj₁' hj₁]

end QTilde
