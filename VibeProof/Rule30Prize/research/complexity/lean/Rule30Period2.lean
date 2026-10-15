import Ruliology.CellularAutomata.Rule30Prize

/-!
# The shape forced near the center by a hypothetical eventual period 2 (scratch)

If the center column were eventually `1, 0, 1, 0, …` from time `T`, then with
`s k = cell (T + 2k + 1) (-1)`:

* column `-1` is black at every even offset (`T + 2k`), and column `1` at odd offsets is `!s k`;
* `s` has no two consecutive zeros (golden mean), from column `1`'s rule;
* columns `-2`, `-3` are `(!s k, !s k)` and `(s k, s (k+1))` on the pair of times `T+2k, T+2k+1`;
* column `-4` is white at every odd offset.

Every eventually 2-periodic center column has this form for some `T` (`normalize`), since the
column is not eventually constant. Further left, no position/phase is forced (checked by
enumeration), so this skeleton alone gives no contradiction.
-/

namespace R30Period2
open Ruliology.CellularAutomata.Rule30Jen Ruliology.CellularAutomata.Rule30Prize

theorem step' (t : Nat) (p a b d : Int) (ha : a = p - 1) (hb : b = p) (hd : d = p + 1) :
    cell (t + 1) p = rule (cell t a) (cell t b) (cell t d) := by
  subst ha hb hd; rfl

section
variable {T : Nat} (h : ∀ k, cell (T + 2 * k) 0 = true ∧ cell (T + 2 * k + 1) 0 = false)
include h

theorem m1_even (k : Nat) : cell (T + 2 * k) (-1) = true := by
  have e := step' (T + 2 * k) 0 (-1) 0 1 rfl rfl rfl
  rw [show T + 2 * k + 1 = T + 2 * k + 1 from rfl, (h k).2, (h k).1] at e
  revert e; cases cell (T + 2 * k) (-1) <;> simp [rule]

theorem p1_odd (k : Nat) : cell (T + 2 * k + 1) 1 = !cell (T + 2 * k + 1) (-1) := by
  have e := step' (T + 2 * k + 1) 0 (-1) 0 1 rfl rfl rfl
  rw [show T + 2 * k + 1 + 1 = T + 2 * (k + 1) by omega, (h (k + 1)).1, (h k).2] at e
  revert e; cases cell (T + 2 * k + 1) (-1) <;> cases cell (T + 2 * k + 1) 1 <;> simp [rule]

theorem m2_even (k : Nat) : cell (T + 2 * k) (-2) = !cell (T + 2 * k + 1) (-1) := by
  have e := step' (T + 2 * k) (-1) (-2) (-1) 0 rfl rfl rfl
  rw [m1_even h k, (h k).1] at e
  rw [e]; cases cell (T + 2 * k) (-2) <;> rfl

theorem m2_odd (k : Nat) : cell (T + 2 * k + 1) (-2) = !cell (T + 2 * k + 1) (-1) := by
  have e := step' (T + 2 * k + 1) (-1) (-2) (-1) 0 rfl rfl rfl
  rw [show T + 2 * k + 1 + 1 = T + 2 * (k + 1) by omega, m1_even h (k + 1), (h k).2] at e
  revert e; cases cell (T + 2 * k + 1) (-2) <;> cases cell (T + 2 * k + 1) (-1) <;> simp [rule]

theorem m3_even (k : Nat) : cell (T + 2 * k) (-3) = cell (T + 2 * k + 1) (-1) := by
  have e := step' (T + 2 * k) (-2) (-3) (-2) (-1) rfl rfl rfl
  rw [m1_even h k, m2_odd h k] at e
  revert e; cases cell (T + 2 * k) (-3) <;> cases cell (T + 2 * k + 1) (-1) <;>
    cases cell (T + 2 * k) (-2) <;> simp [rule]

theorem m3_odd (k : Nat) : cell (T + 2 * k + 1) (-3) = cell (T + 2 * k + 3) (-1) := by
  have e := step' (T + 2 * k + 1) (-2) (-3) (-2) (-1) rfl rfl rfl
  rw [show T + 2 * k + 1 + 1 = T + 2 * (k + 1) by omega, m2_even h (k + 1), m2_odd h k,
    show T + 2 * (k + 1) + 1 = T + 2 * k + 3 by omega] at e
  revert e; cases cell (T + 2 * k + 1) (-3) <;> cases cell (T + 2 * k + 3) (-1) <;>
    cases cell (T + 2 * k + 1) (-1) <;> simp [rule]

/-- `s` has no two consecutive zeros. -/
theorem golden (k : Nat) (hs : cell (T + 2 * k + 1) (-1) = false) :
    cell (T + 2 * k + 3) (-1) = true := by
  have h1 : cell (T + 2 * k + 1) 1 = true := by rw [p1_odd h k, hs]; rfl
  have e1 := step' (T + 2 * k + 1) 1 0 1 2 rfl rfl rfl
  rw [(h k).2, h1] at e1
  have h2 : cell (T + 2 * k + 2) 1 = true := by rw [e1]; rfl
  have e2 := step' (T + 2 * k + 2) 1 0 1 2 rfl rfl rfl
  rw [show T + 2 * k + 2 = T + 2 * (k + 1) by omega, (h (k + 1)).1,
    show T + 2 * (k + 1) = T + 2 * k + 2 by omega, h2] at e2
  have h3 : cell (T + 2 * k + 3) 1 = false := by rw [e2]; rfl
  have := p1_odd h (k + 1)
  rw [show T + 2 * (k + 1) + 1 = T + 2 * k + 3 by omega, h3] at this
  revert this; cases cell (T + 2 * k + 3) (-1) <;> simp

/-- Column `-4` is white at every odd offset. -/
theorem m4_odd (k : Nat) : cell (T + 2 * k + 1) (-4) = false := by
  have e := step' (T + 2 * k + 1) (-3) (-4) (-3) (-2) rfl rfl rfl
  rw [show T + 2 * k + 1 + 1 = T + 2 * (k + 1) by omega, m3_even h (k + 1), m3_odd h k, m2_odd h k,
    show T + 2 * (k + 1) + 1 = T + 2 * k + 3 by omega] at e
  have g := golden h k
  revert e g; cases cell (T + 2 * k + 1) (-4) <;> cases cell (T + 2 * k + 3) (-1) <;>
    cases cell (T + 2 * k + 1) (-1) <;> simp [rule]

end

/-- Every eventual period 2 of the center column has the normalized shape for some `T`. -/
theorem normalize {T0 : Nat} (hp : ∀ t, T0 ≤ t → center (t + 2) = center t) :
    ∃ T, ∀ k, cell (T + 2 * k) 0 = true ∧ cell (T + 2 * k + 1) 0 = false := by
  have per : ∀ k t, T0 ≤ t → center (t + 2 * k) = center t := by
    intro k; induction k with
    | zero => intro t _; rfl
    | succ k ih => intro t ht; rw [show t + 2 * (k + 1) = (t + 2 * k) + 2 by omega, hp _ (by omega), ih t ht]
  have hne : center T0 ≠ center (T0 + 1) := by
    intro e
    apply center_not_eventually_constant
    refine ⟨T0, center T0, fun t ht => ?_⟩
    obtain ⟨k, hk | hk⟩ : ∃ k, t = T0 + 2 * k ∨ t = T0 + 1 + 2 * k := ⟨(t - T0) / 2, by omega⟩
    · rw [hk, per k T0 (by omega)]
    · rw [hk, per k (T0 + 1) (by omega), e]
  cases h0 : center T0
  · refine ⟨T0 + 1, fun k => ⟨?_, ?_⟩⟩
    · have := per k (T0 + 1) (by omega)
      have h1 : center (T0 + 1) = true := by
        cases e : center (T0 + 1)
        · exact absurd (h0.trans e.symm) hne
        · rfl
      exact this.trans h1
    · have := per (k + 1) T0 (Nat.le_refl _)
      rw [show T0 + 2 * (k + 1) = T0 + 1 + 2 * k + 1 by omega] at this
      exact this.trans h0
  · refine ⟨T0, fun k => ⟨(per k T0 (Nat.le_refl _)).trans h0, ?_⟩⟩
    have := per k (T0 + 1) (by omega)
    rw [show T0 + 1 + 2 * k = T0 + 2 * k + 1 by omega] at this
    have h1 : center (T0 + 1) = false := by
      cases e : center (T0 + 1)
      · rfl
      · exact absurd (h0.trans e.symm) hne
    exact this.trans h1

end R30Period2
