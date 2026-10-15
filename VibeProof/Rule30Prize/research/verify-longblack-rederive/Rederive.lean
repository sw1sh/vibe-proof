import Ruliology.CellularAutomata.Rule30Prize

/-!
Verifier's independent re-derivation of the long-black-runs exclusion (does not import or copy
`newideas/BlackRun.lean`; only `Rule30Jen.cell`, `cell_left`, `periodic_mul`, `not_adjacent`).
-/

namespace VerifyLongBlack
open Ruliology.CellularAutomata.Rule30Jen

/-! ### Light cone of the right half -/

/-- One rule-30 pass: left neighbour `l`, current cell `c`, then the cells to the right. -/
def go (l c : Bool) : List Bool → List Bool
  | [] => []
  | r :: rs => xor l (c || r) :: go c r rs

/-- Cells `a, a+1, …, a+n-1` at time `t`. -/
def rowAt (t : Nat) (a : Int) : Nat → List Bool
  | 0 => []
  | n + 1 => cell t a :: rowAt t (a + 1) n

theorem go_rowAt (t : Nat) : ∀ (n : Nat) (a : Int),
    go (cell t (a - 1)) (cell t a) (rowAt t (a + 1) n) = rowAt (t + 1) a n
  | 0, _ => rfl
  | n + 1, a => by
    show xor (cell t (a - 1)) (cell t a || cell t (a + 1)) ::
        go (cell t a) (cell t (a + 1)) (rowAt t (a + 1 + 1) n) = cell (t + 1) a :: rowAt (t + 1) (a + 1) n
    have ih := go_rowAt t n (a + 1)
    rw [show a + 1 - 1 = a by omega] at ih
    rw [ih]
    rfl

/-- One step of columns `1, 2, …` with column `0` black. -/
def stepT : List Bool → List Bool
  | [] => []
  | x :: xs => go true x xs

theorem stepT_rowAt (t n : Nat) (h : cell t 0 = true) :
    stepT (rowAt t 1 (n + 1)) = rowAt (t + 1) 1 n := by
  show go true (cell t 1) (rowAt t (1 + 1) n) = rowAt (t + 1) 1 n
  have e := go_rowAt t n 1
  rw [show (1 : Int) - 1 = 0 by decide, h] at e
  exact e

def iterT : Nat → List Bool → List Bool
  | 0, row => row
  | k + 1, row => iterT k (stepT row)

theorem iterT_rowAt : ∀ (k n t : Nat), (∀ j, j < k → cell (t + j) 0 = true) →
    iterT k (rowAt t 1 (n + k)) = rowAt (t + k) 1 n
  | 0, _, _, _ => rfl
  | k + 1, n, t, h => by
    show iterT k (stepT (rowAt t 1 (n + k + 1))) = rowAt (t + (k + 1)) 1 n
    rw [stepT_rowAt t (n + k) (by simpa using h 0 (by omega))]
    rw [iterT_rowAt k n (t + 1) (fun j hj => by
      rw [show t + 1 + j = t + (j + 1) by omega]; exact h (j + 1) (by omega))]
    rw [show t + 1 + k = t + (k + 1) by omega]

/-- Exhaustive: nine steps with a black column 0 send every row of 11 cells to `(white, black)`. -/
theorem forcing_check : ∀ b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 : Bool,
    iterT 9 [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11] = [false, true] := by
  decide

theorem black_run' (t : Nat) (h : ∀ j, j < 9 → cell (t + j) 0 = true) :
    cell (t + 9) 1 = false ∧ cell (t + 9) 2 = true := by
  have e := iterT_rowAt 9 2 t h
  have hrow : rowAt t 1 (2 + 9) = [cell t 1, cell t 2, cell t 3, cell t 4, cell t 5, cell t 6,
      cell t 7, cell t 8, cell t 9, cell t 10, cell t 11] := rfl
  have hrow2 : rowAt (t + 9) 1 2 = [cell (t + 9) 1, cell (t + 9) 2] := rfl
  rw [hrow, forcing_check, hrow2] at e
  simp only [List.cons.injEq] at e
  exact ⟨e.1.symm, e.2.1.symm⟩

/-! ### Column 1 inside a white run that follows nine blacks -/

theorem col1_step (s : Nat) (hs : cell s 0 = false) (h1 : cell s 1 = true) : cell (s + 1) 1 = true := by
  show rule (cell s (1 - 1)) (cell s 1) (cell s (1 + 1)) = true
  rw [show (1 : Int) - 1 = 0 by decide, hs, h1]
  rfl

theorem col1_start (z : Nat) (hz : cell z 0 = false) (h1 : cell z 1 = false) (h2 : cell z 2 = true) :
    cell (z + 1) 1 = true := by
  show rule (cell z (1 - 1)) (cell z 1) (cell z (1 + 1)) = true
  rw [show (1 : Int) - 1 = 0 by decide, show (1 : Int) + 1 = 2 by decide, hz, h1, h2]
  rfl

/-- If `z ≥ 9`, columns 0 is black at `z-9 … z-1` and white on `[z, t]`, then column 1 at `t`
is `!c(t-1)`. -/
theorem col1_formula (z t : Nat) (hz : 9 ≤ z) (hzt : z ≤ t)
    (hblack : ∀ j, j < 9 → cell (z - 9 + j) 0 = true)
    (hwhite : ∀ s, z ≤ s → s ≤ t → cell s 0 = false) :
    cell t 1 = !cell (t - 1) 0 := by
  have hb := black_run' (z - 9) hblack
  rw [show z - 9 + 9 = z by omega] at hb
  by_cases hzt' : z = t
  · subst hzt'
    have : cell (z - 1) 0 = true := by
      have := hblack 8 (by omega); rwa [show z - 9 + 8 = z - 1 by omega] at this
    rw [this, hb.1]; rfl
  · have hprev : cell (t - 1) 0 = false := hwhite (t - 1) (by omega) (by omega)
    rw [hprev]
    -- column 1 is black on (z, t]
    have hall : ∀ k, z + 1 + k ≤ t → cell (z + 1 + k) 1 = true := by
      intro k
      induction k with
      | zero => intro _; exact col1_start z (hwhite z (by omega) (by omega)) hb.1 hb.2
      | succ k ih =>
        intro hk
        rw [show z + 1 + (k + 1) = (z + 1 + k) + 1 by omega]
        exact col1_step _ (hwhite _ (by omega) (by omega)) (ih (by omega))
    have := hall (t - z - 1) (by omega)
    rw [show z + 1 + (t - z - 1) = t by omega] at this
    rw [this]; rfl

/-! ### Main theorem (hypothesis form) -/

/-- If the center column is periodic from `T` with period `P`, it is not the case that from `T'` on
every white center cell lies in a white run `[z, …]` (with `z ≥ 9`) whose nine predecessors are
black. -/
theorem main (T P T' : Nat) (hP : 0 < P)
    (hper : ∀ t, T ≤ t → cell (t + P) 0 = cell t 0)
    (hrun : ∀ t, T' ≤ t → cell t 0 = false → ∃ z, 9 ≤ z ∧ z ≤ t ∧
      (∀ s, z ≤ s → s ≤ t → cell s 0 = false) ∧ (∀ j, j < 9 → cell (z - 9 + j) 0 = true)) : False := by
  have key : ∀ t, T' ≤ t → cell t 0 = false → cell t 1 = !cell (t - 1) 0 := by
    intro t ht hw
    obtain ⟨z, hz, hzt, hwhite, hblack⟩ := hrun t ht hw
    exact col1_formula z t hz hzt hblack hwhite
  -- column -1 is periodic from T0
  let T0 := max T T' + 1
  have hm1 : ∀ t, T0 ≤ t → cell (t + P) (-1) = cell t (-1) := by
    intro t ht
    have l1 := cell_left (t + P) 0
    have l2 := cell_left t 0
    rw [show (0 : Int) - 1 = -1 by decide, show (0 : Int) + 1 = 1 by decide] at l1 l2
    rw [l1, l2, show t + P + 1 = (t + 1) + P by omega, hper (t + 1) (by omega), hper t (by omega)]
    cases hc : cell t 0 with
    | true => rfl
    | false =>
      have hc' : cell (t + P) 0 = false := by rw [hper t (by omega)]; exact hc
      rw [key t (by omega) hc, key (t + P) (by omega) hc', show t + P - 1 = (t - 1) + P by omega,
        hper (t - 1) (by omega)]
  have h0 : EventuallyPeriodic fun t => cell t ((-1 : Int) + 1) := by
    rw [show (-1 : Int) + 1 = 0 by decide]
    exact ⟨T, P, hP, hper⟩
  exact not_adjacent (-1) ⟨T0, P, hP, hm1⟩ h0

/-! ### Block form: every maximal black run (in the periodic regime) has length ≥ 9 -/

theorem run_start : ∀ m t, m ≤ t → cell (t - m) 0 = true → cell t 0 = false →
    ∃ z, 1 ≤ z ∧ z ≤ t ∧ t - z < m ∧ (∀ s, z ≤ s → s ≤ t → cell s 0 = false) ∧ cell (z - 1) 0 = true
  | 0, t, _, h1, h0 => by simp at h1; rw [h1] at h0; exact absurd h0 (by decide)
  | m + 1, t, hm, h1, h0 => by
    cases hp : cell (t - 1) 0 with
    | true => exact ⟨t, by omega, Nat.le_refl t, by omega, fun s hs1 hs2 => by
        rw [show s = t by omega]; exact h0, hp⟩
    | false =>
      obtain ⟨z, hz1, hzt, hlt, hw, hzb⟩ := run_start m (t - 1) (by omega)
        (by rw [show t - 1 - m = t - (m + 1) by omega]; exact h1) hp
      refine ⟨z, hz1, by omega, by omega, fun s hs1 hs2 => ?_, hzb⟩
      by_cases hst : s = t
      · rw [hst]; exact h0
      · exact hw s hs1 (by omega)

/-- **Block form.** If the center column is periodic from `T` with period `P`, contains a black
cell in the periodic regime, and every black run ending (at `t`, with `c(t+1)` white) after `T''`
has length at least nine, contradiction. (A block with no black cell is the constant case,
excluded separately by `Rule30Prize.center_not_eventually_constant`.) -/
theorem block_form (T P T'' : Nat) (hP : 0 < P)
    (hper : ∀ t, T ≤ t → cell (t + P) 0 = cell t 0)
    (hblack : ∃ t0, T ≤ t0 ∧ cell t0 0 = true)
    (hlong : ∀ t, T'' ≤ t → cell t 0 = true → cell (t + 1) 0 = false →
      ∀ j, j < 9 → cell (t - j) 0 = true) : False := by
  obtain ⟨t0, ht0, hc0⟩ := hblack
  refine main T P (t0 + T'' + P + 12) hP hper ?_
  intro t ht hw
  -- a black cell at distance r ∈ [1, P) before t
  have hdec := Nat.div_add_mod (t - t0) P
  have hrlt := Nat.mod_lt (t - t0) hP
  generalize (t - t0) % P = r at hdec hrlt
  generalize (t - t0) / P = q at hdec
  have hcr : cell (t - r) 0 = true := by
    have : cell (t0 + q * P) 0 = cell t0 0 := periodic_mul (f := fun t => cell t 0) hper q t0 ht0
    rw [show t - r = t0 + q * P by rw [Nat.mul_comm] at hdec; omega, this]
    exact hc0
  have hr0 : r ≠ 0 := by
    intro h0; rw [h0, Nat.sub_zero] at hcr; rw [hcr] at hw; exact absurd hw (by decide)
  obtain ⟨z, hz1, hzt, hlt, hwz, hzb⟩ := run_start r t (by omega) hcr hw
  have hl := hlong (z - 1) (by omega) hzb (by rw [show z - 1 + 1 = z by omega]; exact hwz z (Nat.le_refl z) hzt)
  refine ⟨z, by omega, hzt, hwz, fun j hj => ?_⟩
  have := hl (8 - j) (by omega)
  rwa [show z - 1 - (8 - j) = z - 9 + j by omega] at this

/-! ### Instances -/

/-- The center column is never eventually `(0^a 1^b)^∞` with `a ≥ 1`, `b ≥ 9` (any transient, any
phase: the phase is absorbed into `T`). -/
theorem not_eventually_zeros_ones (a b T : Nat) (ha : 1 ≤ a) (hb : 9 ≤ b)
    (h : ∀ t, T ≤ t → cell t 0 = decide (a ≤ (t - T) % (a + b))) : False := by
  have hP : 0 < a + b := by omega
  refine block_form T (a + b) (T + a + b) hP ?_ ⟨T + a, by omega, ?_⟩ ?_
  · intro t ht
    rw [h (t + (a + b)) (by omega), h t ht, show t + (a + b) - T = (t - T) + (a + b) by omega,
      Nat.add_mod_right]
  · rw [h (T + a) (by omega), show T + a - T = a by omega, Nat.mod_eq_of_lt (by omega)]
    simp
  · intro t ht h1 h0 j hj
    rw [h t (by omega)] at h1
    rw [h (t + 1) (by omega)] at h0
    rw [h (t - j) (by omega)]
    have hdec := Nat.div_add_mod (t - T) (a + b)
    have hrlt := Nat.mod_lt (t - T) hP
    simp only [decide_eq_true_eq] at h1
    simp only [decide_eq_false_iff_not, Nat.not_le] at h0
    simp only [decide_eq_true_eq]
    generalize (t - T) % (a + b) = r at hdec hrlt h1
    generalize (t - T) / (a + b) = q at hdec
    -- r = a + b - 1, otherwise c(t+1) would be black
    have hr : r = a + b - 1 := by
      rcases Nat.lt_or_ge (r + 1) (a + b) with hlt | hge
      · have : (t + 1 - T) % (a + b) = r + 1 := by
          rw [show t + 1 - T = (a + b) * q + (r + 1) by omega, Nat.mul_add_mod,
            Nat.mod_eq_of_lt hlt]
        omega
      · omega
    rw [show t - j - T = (a + b) * q + (r - j) by omega, Nat.mul_add_mod,
      Nat.mod_eq_of_lt (by omega)]
    omega

end VerifyLongBlack

#print axioms VerifyLongBlack.forcing_check
#print axioms VerifyLongBlack.main
#print axioms VerifyLongBlack.block_form
#print axioms VerifyLongBlack.not_eventually_zeros_ones
