import Ruliology.CellularAutomata.Rule30DrivenLeft
namespace Ruliology.CellularAutomata
namespace Q1test
open Rule30Jen Rule30Prize Rule30MaskedJen Rule30DrivenLeft

def stripe (p : Int) : Bool := decide (p % 2 = 1)

theorem stripe_fixed : ∀ t : Nat, ∀ p : Int, p < 0 → L (fun _ => false) stripe t p = stripe p := by
  intro t
  induction t with
  | zero => intro p hp; exact L_zero hp
  | succ t ih =>
    intro p hp
    rw [L_succ hp, ih (p - 1) (by omega), ih p hp]
    by_cases hq : p + 1 < 0
    · rw [ih (p + 1) hq]
      simp only [stripe, rule]
      have : p % 2 = 0 ∨ p % 2 = 1 := by omega
      rcases this with h | h
      · have h1 : (p - 1) % 2 = 1 := by omega
        have h2 : (p + 1) % 2 = 1 := by omega
        simp [h, h1, h2]
      · have h1 : (p - 1) % 2 = 0 := by omega
        have h2 : (p + 1) % 2 = 0 := by omega
        simp [h, h1, h2]
    · have hp1 : p = -1 := by omega
      subst hp1
      rw [show (-1 : Int) + 1 = 0 by rfl, L_col0]
      decide

theorem stripe_col (t : Nat) : L (fun _ => false) stripe t (-1) = true := by
  rw [stripe_fixed t (-1) (by omega)]; decide

theorem effective_white {T : Nat} (h : ∀ k, cell (T + 2 * k) 0 = true ∧ cell (T + 2 * k + 1) 0 = false)
    (k : Nat) : (center (T + k) && center (T + k + 1)) = false := by
  obtain ⟨j, rfl | rfl⟩ : ∃ j, k = 2 * j ∨ k = 2 * j + 1 := ⟨k / 2, by omega⟩
  · show (cell (T + 2 * j) 0 && cell (T + 2 * j + 1) 0) = false
    rw [(h j).2]; cases cell (T + 2 * j) 0 <;> rfl
  · show (cell (T + (2 * j + 1)) 0 && cell (T + (2 * j + 1) + 1) 0) = false
    rw [show T + (2 * j + 1) = T + 2 * j + 1 by omega, (h j).2]; rfl

theorem left_half_zero_driven {T : Nat}
    (h : ∀ k, cell (T + 2 * k) 0 = true ∧ cell (T + 2 * k + 1) 0 = false) :
    ∀ k : Nat, ∀ p : Int, p < 0 → L (fun _ => false) (fun p => cell T p) k p = cell (T + k) p := by
  have hfun : (fun k => center (T + k) && center (T + k + 1)) = fun _ => false :=
    funext (effective_white h)
  intro k p hp
  have := cell_eq_L_effective T k p hp
  rwa [hfun] at this

end Q1test
end Ruliology.CellularAutomata
