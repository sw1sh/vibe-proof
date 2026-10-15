import Ruliology.CellularAutomata.Rule30Jen

/-!
# The zero-boundary left half (ZBL) of Rule 30 under the period-2 constraint

If the center column of Rule 30 alternates from time `T` on, the left half evolves as Rule 30 on the cells
`p ≤ -1` with column `0` forced white (effective boundary `c(t) && c(t+1) = 0`), and column `-1` must be black at
every other step.  We use mirrored coordinates: for a configuration `x : Nat → Bool`, `x k` (`k ≥ 1`) is the cell at
depth `k` (that is, `cell t (-k)`), and `x 0` is the white wall.  One step of the ZBL is

  `step x 0 = false`,   `step x (k+1) = xor (x (k+2)) (x (k+1) || x k)`.

The phase-0 constraint is `run x (2*j) 1 = true` for every `j`; question Q_01 asks whether a finitely supported `x`
can satisfy it forever.  The stripe `s` (black exactly at odd depths, `...10101`) is a fixed point satisfying it.

Main results (all for arbitrary configurations with a white wall):
* `first_defect_run`, `first_defect_hits`, `first_defect_even`, `first_defect_parity`: the first deviation from the stripe moves one cell
  toward the wall per step; hence in a constrained history the first deviation is at an even depth at even times,
  and a deviation at odd depth `d` kills the history at time `d - 1`.
* `free_bit`, `reset_config`: the free bit at an odd time is 0 exactly when the first deviation (one step earlier) is
  at depth 2; at such a reset the configuration is `0, 1, s 3, …, s d`, deviating again at depth `d + 1`, where `d`
  (even) is the first-deviation depth one step later, i.e. the length of the next epoch.
* `agrees_two_steps`: if `x` equals the stripe from depth `L ≥ 1` on, so does `step (step x)` (the last deviation from
  the stripe never moves outward over two steps; contrast with the zero background, into which Rule 30 expands).
* `agrees_pre`: a preimage of a configuration that is the stripe from depth `L` on is the stripe from depth `L + 4` on.
* `agrees_pre_run`, `finite_never_stripe`: backward orbits of stripe-tailed configurations stay stripe-tailed; a
  finitely supported configuration never evolves into a stripe-tailed one.
* `col1_not_eventually_true`: for a finitely supported start, column 1 is not eventually constantly black, i.e. the
  free bits of a constrained history cannot be eventually 1.
* `col1_periodic_white`, `constrained_col1_aperiodic`: Jen's argument in the ZBL: for a finitely supported start,
  an eventually periodic column 1 is eventually white; so under the constraint column 1 is not eventually periodic.
* `q01_width_le_16`: Q_01 for every start of width at most 16, by a kernel-checked exhaustive search
  (`decide +kernel` on packed configurations, with the bridge `step_toFun`, `exists_pack`).
* Bridge to `Rule30Jen.cell`: `alt_left_run` (an alternating center makes the left half a ZBL),
  `alt_first_defect_parity` (the first deviation of the true left half from `…10101` has the parity of the phase),
  `alt_col_neg1_aperiodic`, and `not_alt_small` (no alternation from `T ≤ 15`; far weaker than the window bound,
  included as a consistency check of the bridge).
-/

namespace ZBL

/-! ## Stripe -/

def s (k : Nat) : Bool := k % 2 == 1

theorem s_succ (k : Nat) : s (k + 1) = !s k := by
  unfold s
  rcases Nat.mod_two_eq_zero_or_one k with h | h
  · have : (k + 1) % 2 = 1 := by omega
    simp [h, this]
  · have : (k + 1) % 2 = 0 := by omega
    simp [h, this]

theorem s_add_two (k : Nat) : s (k + 2) = s k := by
  rw [s_succ, s_succ]; simp

theorem s_or (k : Nat) : (s (k + 1) || s k) = true := by
  rw [s_succ]; cases s k <;> rfl

theorem s_zero : s 0 = false := rfl
theorem s_one : s 1 = true := rfl
theorem s_odd {k : Nat} (h : k % 2 = 1) : s k = true := by unfold s; simp [h]
theorem s_even {k : Nat} (h : k % 2 = 0) : s k = false := by unfold s; simp [h]

/-! ## Dynamics -/

def step (x : Nat → Bool) : Nat → Bool
  | 0 => false
  | k + 1 => xor (x (k + 2)) (x (k + 1) || x k)

def run (x : Nat → Bool) : Nat → Nat → Bool
  | 0 => x
  | t + 1 => step (run x t)

theorem step_zero (x : Nat → Bool) : step x 0 = false := rfl
theorem step_succ (x : Nat → Bool) (k : Nat) :
    step x (k + 1) = xor (x (k + 2)) (x (k + 1) || x k) := rfl
theorem run_zero (x : Nat → Bool) : run x 0 = x := rfl
theorem run_succ (x : Nat → Bool) (t : Nat) : run x (t + 1) = step (run x t) := rfl

theorem run_add (x : Nat → Bool) (t i : Nat) : run x (t + i) = run (run x t) i := by
  induction i with
  | zero => rfl
  | succ i ih => rw [← Nat.add_assoc, run_succ, run_succ, ih]

theorem run_wall {x : Nat → Bool} (hw : x 0 = false) (t : Nat) : run x t 0 = false := by
  cases t with
  | zero => exact hw
  | succ t => rfl

/-- The stripe is a fixed point of the ZBL. -/
theorem step_s : step s = s := by
  funext k
  cases k with
  | zero => rfl
  | succ k =>
    rw [step_succ, s_or, s_succ (k + 1), s_succ k]
    cases s k <;> rfl

/-- Left-permutive inversion: column `k + 2` is recovered from columns `k`, `k + 1`. -/
theorem inv_step (x : Nat → Bool) (k : Nat) :
    x (k + 2) = xor (step x (k + 1)) (x (k + 1) || x k) := by
  rw [step_succ]; cases x (k + 2) <;> cases (x (k + 1) || x k) <;> rfl

/-! ## The first deviation from the stripe -/

/-- If `x` agrees with the stripe on depths `1, …, d-1` and deviates at depth `d ≥ 2`, then `step x` agrees with the
stripe on depths `1, …, d-2` and deviates at depth `d - 1`. -/
theorem first_defect_step (x : Nat → Bool) (hw : x 0 = false) (d : Nat) (hd : 2 ≤ d)
    (hag : ∀ k, 1 ≤ k → k < d → x k = s k) (hne : x d ≠ s d) :
    (∀ k, 1 ≤ k → k < d - 1 → step x k = s k) ∧ step x (d - 1) ≠ s (d - 1) := by
  have hj : ∀ j, j + 1 < d → x j = s j := by
    intro j hj
    cases j with
    | zero => rw [hw]; rfl
    | succ j => exact hag (j + 1) (by omega) (by omega)
  constructor
  · intro k hk1 hk2
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [step_succ, hag (j + 2) (by omega) (by omega), hag (j + 1) (by omega) (by omega),
      hj j (by omega), ← step_succ, step_s]
  · obtain ⟨j, rfl⟩ : ∃ j, d = j + 2 := ⟨d - 2, by omega⟩
    rw [show j + 2 - 1 = j + 1 by omega, step_succ, hag (j + 1) (by omega) (by omega),
      hj j (by omega), s_or]
    rw [show j + 2 = (j + 1) + 1 by omega, s_succ (j + 1)] at hne
    rw [show j + 2 = (j + 1) + 1 by omega]
    revert hne
    cases x (j + 1 + 1) <;> cases s (j + 1) <;> simp

/-- The first deviation travels to depth 1 at speed one. -/
theorem first_defect_run (x : Nat → Bool) (hw : x 0 = false) (d : Nat)
    (hag : ∀ k, 1 ≤ k → k < d → x k = s k) (hne : x d ≠ s d) :
    ∀ i, i + 1 ≤ d → (∀ k, 1 ≤ k → k < d - i → run x i k = s k) ∧ run x i (d - i) ≠ s (d - i) := by
  intro i
  induction i with
  | zero => intro _; exact ⟨hag, hne⟩
  | succ i ih =>
    intro hi
    obtain ⟨h1, h2⟩ := ih (by omega)
    have := first_defect_step (run x i) (run_wall hw i) (d - i) (by omega) h1 h2
    rw [run_succ, show d - (i + 1) = d - i - 1 by omega]
    exact this

/-- A deviation at depth `d ≥ 1` turns depth 1 white at time `d - 1`. -/
theorem first_defect_hits (x : Nat → Bool) (hw : x 0 = false) (d : Nat) (hd : 1 ≤ d)
    (hag : ∀ k, 1 ≤ k → k < d → x k = s k) (hne : x d ≠ s d) : run x (d - 1) 1 = false := by
  have := (first_defect_run x hw d hag hne (d - 1) (by omega)).2
  rw [show d - (d - 1) = 1 by omega, s_one] at this
  revert this; cases run x (d - 1) 1 <;> simp

/-- Phase-0 constraint up to time `N`: depth 1 is black at every even time `≤ N`. -/
def Constrained (x : Nat → Bool) (N : Nat) : Prop := ∀ j, 2 * j ≤ N → run x (2 * j) 1 = true

/-- In a constrained history the first deviation from the stripe (if it is reached by time `N`) lies at an
even depth. -/
theorem first_defect_even (x : Nat → Bool) (hw : x 0 = false) (N d : Nat) (hd : 1 ≤ d) (hdN : d ≤ N + 1)
    (hag : ∀ k, 1 ≤ k → k < d → x k = s k) (hne : x d ≠ s d) (hc : Constrained x N) : d % 2 = 0 := by
  rcases Nat.mod_two_eq_zero_or_one d with h | h
  · exact h
  · exfalso
    have h1 := first_defect_hits x hw d hd hag hne
    have h2 := hc ((d - 1) / 2) (by omega)
    rw [show 2 * ((d - 1) / 2) = d - 1 by omega] at h2
    rw [h1] at h2; cases h2

/-- Same statement at any time `t`: the first deviation of `run x t` from the stripe sits at a depth `d` with
`t + d` even (whenever `t + d - 1 ≤ N`). -/
theorem first_defect_parity (x : Nat → Bool) (hw : x 0 = false) (N t d : Nat) (hd : 1 ≤ d)
    (hdN : t + d ≤ N + 1) (hag : ∀ k, 1 ≤ k → k < d → run x t k = s k) (hne : run x t d ≠ s d)
    (hc : Constrained x N) : (t + d) % 2 = 0 := by
  rcases Nat.mod_two_eq_zero_or_one (t + d) with h | h
  · exact h
  · exfalso
    have h1 := first_defect_hits (run x t) (run_wall hw t) d hd hag hne
    rw [← run_add, show t + (d - 1) = t + d - 1 by omega] at h1
    have h2 := hc ((t + d - 1) / 2) (by omega)
    rw [show 2 * ((t + d - 1) / 2) = t + d - 1 by omega] at h2
    rw [h1] at h2; cases h2

/-- The free bit at an odd time vanishes exactly when the first deviation (at the preceding even time) is at
depth 2: if depth 1 is black, `step x 1 = !x 2`. -/
theorem free_bit (x : Nat → Bool) (hw : x 0 = false) (h1 : x 1 = true) : step x 1 = !x 2 := by
  rw [step_succ, h1, hw]; cases x 2 <;> rfl

/-- **Configuration at a reset.** If depth 1 is white at time `τ` and `step x` first deviates from the stripe at
depth `d ≥ 2`, then at time `τ` the configuration is `0, 1, s 3, …, s d` followed by a deviation at depth `d + 1`.
(In a constrained history `d` is even, by `first_defect_parity`.) -/
theorem reset_config (x : Nat → Bool) (hw : x 0 = false) (h1 : x 1 = false) (d : Nat) (hd : 2 ≤ d)
    (hag : ∀ k, 1 ≤ k → k < d → step x k = s k) (hne : step x d ≠ s d) :
    x 2 = true ∧ (∀ k, 3 ≤ k → k ≤ d → x k = s k) ∧ x (d + 1) ≠ s (d + 1) := by
  have h2 : x 2 = true := by
    rw [inv_step x 0, hag 1 (by omega) (by omega), h1, hw]; rfl
  have mid : ∀ k, 3 ≤ k → k ≤ d → x k = s k := by
    intro k
    induction k using Nat.strongRecOn with
    | ind k ih =>
      intro hk3 hkd
      obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
      rw [inv_step x j, hag (j + 1) (by omega) (by omega)]
      have hor : (x (j + 1) || x j) = true := by
        rcases Nat.lt_or_ge j 2 with hj | hj
        · obtain rfl : j = 1 := by omega
          rw [h2]; rfl
        · rcases Nat.lt_or_ge j 3 with hj3 | hj3
          · obtain rfl : j = 2 := by omega
            rw [ih 3 (by omega) (by omega) (by omega)]; rfl
          · rw [ih (j + 1) (by omega) (by omega) (by omega), ih j (by omega) (by omega) (by omega), s_or]
      rw [hor, show j + 2 = (j + 1) + 1 by omega, s_succ (j + 1)]
      cases s (j + 1) <;> rfl
  refine ⟨h2, mid, ?_⟩
  obtain ⟨j, rfl⟩ : ∃ j, d = j + 1 := ⟨d - 1, by omega⟩
  rw [show j + 1 + 1 = j + 2 by omega, inv_step x j]
  have hor : (x (j + 1) || x j) = true := by
    rcases Nat.lt_or_ge j 2 with hj | hj
    · obtain rfl : j = 1 := by omega
      rw [h2]; rfl
    · rcases Nat.lt_or_ge j 3 with hj3 | hj3
      · obtain rfl : j = 2 := by omega
        rw [mid 3 (by omega) (by omega)]; rfl
      · rw [mid (j + 1) (by omega) (by omega), mid j (by omega) (by omega), s_or]
  rw [hor, show j + 2 = (j + 1) + 1 by omega, s_succ (j + 1)]
  intro h; apply hne
  revert h; cases step x (j + 1) <;> cases s (j + 1) <;> simp

/-! ## The last deviation from the stripe -/

/-- `x` equals the stripe from depth `L` on. -/
def AgreesFrom (x : Nat → Bool) (L : Nat) : Prop := ∀ k, L ≤ k → x k = s k

theorem agrees_step (x : Nat → Bool) (L : Nat) (hL : 1 ≤ L) (h : AgreesFrom x L) :
    AgreesFrom (step x) (L + 1) := by
  intro k hk
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [step_succ, h (j + 2) (by omega), h (j + 1) (by omega), h j (by omega), ← step_succ, step_s]

theorem agrees_step_odd (x : Nat → Bool) (L : Nat) (hL : L % 2 = 1) (h : AgreesFrom x L) :
    AgreesFrom (step x) L := by
  intro k hk
  rcases Nat.lt_or_eq_of_le hk with hk | hk
  · exact agrees_step x L (by omega) h k (by omega)
  · subst hk
    obtain ⟨j, rfl⟩ : ∃ j, L = j + 1 := ⟨L - 1, by omega⟩
    rw [step_succ, h (j + 2) (by omega), h (j + 1) (by omega), s_odd (k := j + 1) hL,
      show j + 2 = (j + 1) + 1 by omega, s_succ (j + 1), s_odd (k := j + 1) hL]
    rfl

theorem agrees_step_odd_defect (x : Nat → Bool) (L : Nat) (hL : L % 2 = 1) (hL3 : 3 ≤ L)
    (h : AgreesFrom x L) (hne : x (L - 1) ≠ s (L - 1)) : AgreesFrom (step x) (L - 1) := by
  intro k hk
  rcases Nat.lt_or_eq_of_le hk with hk | hk
  · exact agrees_step_odd x L hL h k (by omega)
  · subst hk
    obtain ⟨j, rfl⟩ : ∃ j, L = j + 2 := ⟨L - 2, by omega⟩
    have hev : (j + 1) % 2 = 0 := by omega
    have hx : x (j + 1) = true := by
      rw [show j + 2 - 1 = j + 1 by omega, s_even hev] at hne
      revert hne; cases x (j + 1) <;> simp
    rw [show j + 2 - 1 = j + 1 by omega, step_succ, h (j + 2) (by omega), hx,
      s_odd (k := j + 2) hL, s_even hev]
    rfl

theorem step_even_defect (x : Nat → Bool) (L : Nat) (hL : L % 2 = 0) (hL2 : 2 ≤ L)
    (h : AgreesFrom x L) (hne : x (L - 1) ≠ s (L - 1)) : step x L ≠ s L := by
  obtain ⟨j, rfl⟩ : ∃ j, L = j + 1 := ⟨L - 1, by omega⟩
  have hodd : j % 2 = 1 := by omega
  have hx : x j = false := by
    rw [show j + 1 - 1 = j by omega, s_odd hodd] at hne
    revert hne; cases x j <;> simp
  rw [step_succ, h (j + 2) (by omega), h (j + 1) (by omega), hx, s_even hL,
    s_odd (k := j + 2) (by omega)]
  simp

/-- **The last deviation from the stripe never moves outward over two steps.** -/
theorem agrees_two_steps (x : Nat → Bool) (L : Nat) (hL : 1 ≤ L) (h : AgreesFrom x L) :
    AgreesFrom (step (step x)) L := by
  rcases Nat.mod_two_eq_zero_or_one L with he | ho
  · -- L even, L ≥ 2
    by_cases hd : x (L - 1) = s (L - 1)
    · have h' : AgreesFrom x (L - 1) := by
        intro k hk
        rcases Nat.lt_or_eq_of_le hk with hk | hk
        · exact h k (by omega)
        · subst hk; exact hd
      have h1 := agrees_step_odd x (L - 1) (by omega) h'
      have h2 := agrees_step (step x) (L - 1) (by omega) h1
      rw [show L - 1 + 1 = L by omega] at h2
      exact h2
    · have h1 := agrees_step x L hL h
      have h2 := step_even_defect x L he (by omega) h hd
      have h3 := agrees_step_odd_defect (step x) (L + 1) (by omega) (by omega) h1
        (by rw [show L + 1 - 1 = L by omega]; exact h2)
      rw [show L + 1 - 1 = L by omega] at h3
      exact h3
  · exact agrees_step_odd (step x) L ho (agrees_step_odd x L ho h)

theorem agrees_run_even (x : Nat → Bool) (L : Nat) (hL : 1 ≤ L) (h : AgreesFrom x L) (t : Nat) :
    AgreesFrom (run x (2 * t)) L := by
  induction t with
  | zero => exact h
  | succ t ih =>
    rw [show 2 * (t + 1) = 2 * t + 1 + 1 by omega, run_succ, run_succ]
    exact agrees_two_steps _ L hL ih

/-! ## Preimages of stripe-tailed configurations -/

/-- If `step y` equals the stripe from depth `L ≥ 1` on, then `y` equals the stripe from depth `L + 4` on. -/
theorem agrees_pre (y : Nat → Bool) (L : Nat) (hL : 1 ≤ L) (h : AgreesFrom (step y) L) :
    AgreesFrom y (L + 4) := by
  -- recurrence y (k+2) = xor (s (k+1)) (y (k+1) || y k) for k + 1 ≥ L
  have hrec : ∀ k, L ≤ k + 1 → y (k + 2) = xor (s (k + 1)) (y (k + 1) || y k) := by
    intro k hk; rw [inv_step y k, h (k + 1) hk]
  -- once two consecutive depths agree (at depths ≥ L - 1), all later depths agree
  have prop : ∀ m, L ≤ m + 1 → y m = s m → y (m + 1) = s (m + 1) → ∀ i, y (m + i) = s (m + i) := by
    intro m hm h0 h1 i
    induction i using Nat.strongRecOn with
    | ind i ih =>
      match i, ih with
      | 0, _ => exact h0
      | 1, _ => exact h1
      | i + 2, ih =>
        rw [show m + (i + 2) = (m + i) + 2 by omega, hrec (m + i) (by omega),
          show m + i + 1 = m + (i + 1) by omega, ih (i + 1) (by omega), ih i (by omega),
          show m + (i + 1) = (m + i) + 1 by omega, s_or, s_succ (m + i + 1), s_succ (m + i)]
        cases s (m + i) <;> rfl
  obtain ⟨L', rfl⟩ : ∃ L', L = L' + 1 := ⟨L - 1, by omega⟩
  have e2 : y (L' + 2) = xor (!s L') (y (L' + 1) || y L') := by
    rw [hrec L' (by omega), s_succ]
  have e3 : y (L' + 3) = xor (s L') (y (L' + 2) || y (L' + 1)) := by
    rw [hrec (L' + 1) (by omega), show L' + 1 + 1 = L' + 2 by omega, s_add_two]
  have e4 : y (L' + 4) = xor (!s L') (y (L' + 3) || y (L' + 2)) := by
    rw [hrec (L' + 2) (by omega), show L' + 2 + 1 = L' + 3 by omega,
      show L' + 3 = (L' + 1) + 2 by omega, s_add_two, s_succ]
  have e5 : y (L' + 5) = xor (s L') (y (L' + 4) || y (L' + 3)) := by
    rw [hrec (L' + 3) (by omega), show L' + 3 + 1 = L' + 4 by omega,
      show L' + 4 = L' + 2 + 2 by omega, s_add_two, s_add_two]
  have e6 : y (L' + 6) = xor (!s L') (y (L' + 5) || y (L' + 4)) := by
    rw [hrec (L' + 4) (by omega), show L' + 4 + 1 = L' + 5 by omega,
      show L' + 5 = (L' + 1) + 2 + 2 by omega, s_add_two, s_add_two, s_succ]
  have s5 : s (L' + 5) = !s L' := by
    rw [show L' + 5 = (L' + 1) + 2 + 2 by omega, s_add_two, s_add_two, s_succ]
  have s6 : s (L' + 6) = s L' := by
    rw [show L' + 6 = L' + 2 + 2 + 2 by omega, s_add_two, s_add_two, s_add_two]
  have key : y (L' + 5) = s (L' + 5) ∧ y (L' + 6) = s (L' + 6) := by
    rw [e6, e5, e4, e3, e2, s5, s6]
    cases s L' <;> cases y (L' + 1) <;> cases y L' <;> decide
  intro k hk
  have := prop (L' + 5) (by omega) key.1 key.2 (k - (L' + 5))
  rw [show L' + 5 + (k - (L' + 5)) = k by omega] at this
  exact this

/-! ## Finite configurations -/

/-- `x` is white beyond depth `W`. -/
def FiniteW (x : Nat → Bool) (W : Nat) : Prop := ∀ k, W < k → x k = false

theorem finite_step (x : Nat → Bool) (W : Nat) (hx : FiniteW x W) : FiniteW (step x) (W + 1) := by
  intro k hk
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [step_succ, hx (j + 2) (by omega), hx (j + 1) (by omega), hx j (by omega)]; rfl

theorem finite_run (x : Nat → Bool) (W : Nat) (hx : FiniteW x W) (t : Nat) : FiniteW (run x t) (W + t) := by
  induction t with
  | zero => simpa using hx
  | succ t ih => rw [run_succ, show W + (t + 1) = (W + t) + 1 by omega]; exact finite_step _ _ ih

theorem agrees_pre_run (x : Nat → Bool) (L : Nat) (hL : 1 ≤ L) :
    ∀ t, AgreesFrom (run x t) L → AgreesFrom x (L + 4 * t) := by
  intro t
  induction t generalizing L with
  | zero => intro h; simpa using h
  | succ t ih =>
    intro h
    rw [run_succ] at h
    have := ih (L + 4) (by omega) (agrees_pre (run x t) L hL h)
    rw [show L + 4 + 4 * t = L + 4 * (t + 1) by omega] at this
    exact this

/-- A finitely supported configuration never evolves into the stripe (not even from some depth `L` on).
(Immediate from the light cone; the preimage lemma `agrees_pre_run` gives the stronger statement that every
backward orbit of a stripe-tailed configuration stays stripe-tailed.) -/
theorem finite_never_stripe (x : Nat → Bool) (W : Nat) (hx : FiniteW x W) (L t : Nat) :
    ¬ AgreesFrom (run x t) L := by
  intro h
  have h1 := h (2 * (W + L + t) + 1) (by omega)
  rw [finite_run x W hx t _ (by omega), s_odd (by omega)] at h1
  cases h1

/-- Reconstruction: if depth 1 is black at all times `≥ T`, the configuration at time `T` is the stripe. -/
theorem col1_true_stripe (x : Nat → Bool) (hw : x 0 = false) (T : Nat)
    (h : ∀ t, T ≤ t → run x t 1 = true) : ∀ k, ∀ t, T ≤ t → run x t k = s k := by
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    match k, ih with
    | 0, _ => intro t _; rw [run_wall hw]; rfl
    | 1, _ => intro t ht; rw [h t ht]; rfl
    | k + 2, ih =>
      intro t ht
      rw [inv_step (run x t) k, ← run_succ, ih (k + 1) (by omega) (t + 1) (by omega),
        ih (k + 1) (by omega) t ht, ih k (by omega) t ht, s_or, s_succ (k + 1), s_succ k]
      cases s k <;> rfl

/-- **For a finitely supported start, column 1 (depth 1) is not eventually constantly black.**  In a constrained
history this says the free bits are not eventually 1. -/
theorem col1_not_eventually_true (x : Nat → Bool) (hw : x 0 = false) (W : Nat) (hx : FiniteW x W) :
    ¬ ∃ T, ∀ t, T ≤ t → run x t 1 = true := by
  rintro ⟨T, hT⟩
  apply finite_never_stripe x W hx 1 T
  intro k _
  exact col1_true_stripe x hw T hT k T (Nat.le_refl T)

/-! ## Jen's argument in the ZBL: column 1 of a finite start is not eventually periodic (unless eventually white) -/

/-- If column 1 is periodic from time `T` (period `P ≥ 1`), every column is. -/
theorem all_columns_periodic (x : Nat → Bool) (hw : x 0 = false) (T P : Nat)
    (hper : ∀ t, T ≤ t → run x (t + P) 1 = run x t 1) :
    ∀ k, ∀ t, T ≤ t → run x (t + P) k = run x t k := by
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    match k, ih with
    | 0, _ => intro t _; rw [run_wall hw, run_wall hw]
    | 1, _ => exact hper
    | k + 2, ih =>
      intro t ht
      rw [inv_step (run x (t + P)) k, inv_step (run x t) k, ← run_succ, ← run_succ,
        show t + P + 1 = (t + 1) + P by omega, ih (k + 1) (by omega) (t + 1) (by omega),
        ih (k + 1) (by omega) t ht, ih k (by omega) t ht]

/-- **Jen's argument for the ZBL.** For a finitely supported start, if column 1 is eventually periodic then it is
eventually white. -/
theorem col1_periodic_white (x : Nat → Bool) (hw : x 0 = false) (W : Nat) (hx : FiniteW x W) (T P : Nat)
    (hP : 1 ≤ P) (hper : ∀ t, T ≤ t → run x (t + P) 1 = run x t 1) :
    ∀ t, T ≤ t → run x t 1 = false := by
  have per := all_columns_periodic x hw T P hper
  -- far columns are white from time T on
  have far : ∀ k, W + T + P < k → ∀ t, T ≤ t → run x t k = false := by
    intro k hk t
    induction t using Nat.strongRecOn with
    | ind t iht =>
      intro ht
      by_cases h : t < T + P
      · exact finite_run x W hx t k (by omega)
      · rw [show t = (t - P) + P by omega, per k (t - P) (by omega)]
        exact iht (t - P) (by omega) (by omega)
  -- downward induction on the column index
  have down : ∀ j, ∀ k, 1 ≤ k → W + T + P + 1 ≤ k + j → ∀ t, T ≤ t → run x t k = false := by
    intro j
    induction j with
    | zero => intro k _ hk t ht; exact far k (by omega) t ht
    | succ j ihj =>
      intro k hk1 hk t ht
      by_cases hk' : W + T + P + 1 ≤ k + j
      · exact ihj k hk1 hk' t ht
      · have h1 := ihj (k + 1) (by omega) (by omega) (t + 1) (by omega)
        have h2 := ihj (k + 2) (by omega) (by omega) t ht
        have h3 := ihj (k + 1) (by omega) (by omega) t ht
        obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
        rw [run_succ, step_succ, h2, h3] at h1
        revert h1; cases run x t (k' + 1) <;> simp
  exact down (W + T + P) 1 (by omega) (by omega)

/-- **Under the period-2 constraint, column 1 of a finitely supported start is not eventually periodic.**
(Equivalently: the free bits of a constrained history from a finite start are not eventually periodic.) -/
theorem constrained_col1_aperiodic (x : Nat → Bool) (hw : x 0 = false) (W : Nat) (hx : FiniteW x W)
    (hc : ∀ j, run x (2 * j) 1 = true) :
    ¬ ∃ T P, 1 ≤ P ∧ ∀ t, T ≤ t → run x (t + P) 1 = run x t 1 := by
  rintro ⟨T, P, hP, hper⟩
  have := col1_periodic_white x hw W hx T P hP hper (2 * T) (by omega)
  rw [hc T] at this; cases this

/-! ## Packed configurations and a kernel-checked finite verification -/

def toFun (r : Nat) : Nat → Bool := fun k => if k = 0 then false else r.testBit (k - 1)

def pstep (r : Nat) : Nat := (r >>> 1) ^^^ (r ||| (r <<< 1))

theorem step_toFun (r : Nat) : step (toFun r) = toFun (pstep r) := by
  funext k
  cases k with
  | zero => rfl
  | succ k =>
    simp only [step_succ, toFun, pstep, Nat.testBit_xor, Nat.testBit_or, Nat.testBit_shiftRight,
      Nat.testBit_shiftLeft]
    cases k with
    | zero => simp
    | succ j =>
      simp [show 1 + (j + 1) = j + 2 by omega]

def prun (r : Nat) : Nat → Nat
  | 0 => r
  | t + 1 => pstep (prun r t)

theorem run_toFun (r t : Nat) : run (toFun r) t = toFun (prun r t) := by
  induction t with
  | zero => rfl
  | succ t ih => rw [run_succ, ih, step_toFun]; rfl

theorem testBit_ge_of_lt {r W j : Nat} (h : r < 2 ^ W) (hj : W ≤ j) : r.testBit j = false := by
  apply Nat.testBit_lt_two_pow
  exact Nat.lt_of_lt_of_le h (Nat.pow_le_pow_right (by omega) hj)

/-- Every finitely supported configuration with a white wall is packed by some `r < 2 ^ W`. -/
theorem exists_pack (W : Nat) : ∀ x : Nat → Bool, x 0 = false → FiniteW x W →
    ∃ r, r < 2 ^ W ∧ toFun r = x := by
  induction W with
  | zero =>
    intro x hw hx
    refine ⟨0, by decide, ?_⟩
    funext k
    cases k with
    | zero => simp [toFun, hw]
    | succ k => simp [toFun, hx (k + 1) (by omega)]
  | succ W ih =>
    intro x hw hx
    let x' : Nat → Bool := fun k => if k = W + 1 then false else x k
    have hx' : FiniteW x' W := by
      intro k hk
      by_cases h : k = W + 1
      · simp [x', h]
      · simp only [x', h, if_false]; exact hx k (by omega)
    obtain ⟨r', hr', hr'x⟩ := ih x' (by simp [x', hw]) hx'
    have hrx : ∀ k, k ≠ W + 1 → toFun r' k = x k := by
      intro k hk; rw [hr'x]; simp [x', hk]
    cases hb : x (W + 1) with
    | false =>
      refine ⟨r', by rw [Nat.pow_succ]; omega, ?_⟩
      funext k
      by_cases hk : k = W + 1
      · subst hk; rw [hb]; simp [toFun, testBit_ge_of_lt hr' (Nat.le_refl W)]
      · exact hrx k hk
    | true =>
      refine ⟨2 ^ W + r', by rw [Nat.pow_succ]; omega, ?_⟩
      funext k
      by_cases hk : k = W + 1
      · subst hk; rw [hb]
        simp [toFun, Nat.testBit_two_pow_add_eq, testBit_ge_of_lt hr' (Nat.le_refl W)]
      · rw [← hrx k hk]
        simp only [toFun]
        by_cases hk0 : k = 0
        · simp [hk0]
        · simp only [hk0, if_false]
          by_cases hlt : k - 1 < W
          · exact Nat.testBit_two_pow_add_gt hlt r'
          · have h1 : (2 ^ W + r').testBit (k - 1) = false := by
              apply testBit_ge_of_lt (W := W + 1) (by rw [Nat.pow_succ]; omega) (by omega)
            rw [h1, testBit_ge_of_lt hr' (by omega)]

/-- `diesBy n t r`: within `n` steps starting at time `t`, depth 1 is white at some even time. -/
def diesBy : Nat → Nat → Nat → Bool
  | 0, _, _ => false
  | n + 1, t, r => (t % 2 == 0 && r % 2 == 0) || diesBy n (t + 1) (pstep r)

theorem diesBy_sound : ∀ n t r, diesBy n t r = true →
    ∃ i, i < n ∧ (t + i) % 2 = 0 ∧ prun r i % 2 = 0 := by
  intro n
  induction n with
  | zero => intro t r h; simp [diesBy] at h
  | succ n ih =>
    intro t r h
    simp only [diesBy, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
    rcases h with ⟨h1, h2⟩ | h
    · exact ⟨0, by omega, by simpa using h1, h2⟩
    · obtain ⟨i, hi, hti, hpi⟩ := ih (t + 1) (pstep r) h
      refine ⟨i + 1, by omega, by rw [show t + (i + 1) = t + 1 + i by omega]; exact hti, ?_⟩
      have : prun r (i + 1) = prun (pstep r) i := by
        clear hi hti hpi h ih
        induction i generalizing r with
        | zero => rfl
        | succ i ihi => simp only [prun] at *; rw [ihi]
      rw [this]; exact hpi

/-- Check all packed configurations `r < m`. -/
def checkBelow (n : Nat) : Nat → Bool
  | 0 => true
  | m + 1 => diesBy n 0 m && checkBelow n m

theorem checkBelow_sound (n : Nat) : ∀ m, checkBelow n m = true → ∀ r, r < m → diesBy n 0 r = true := by
  intro m
  induction m with
  | zero => intro _ r hr; omega
  | succ m ih =>
    intro h r hr
    simp only [checkBelow, Bool.and_eq_true] at h
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hr) with hr | hr
    · exact ih h.2 r hr
    · subst hr; exact h.1

/-- Soundness: a successful check certifies Q_01 for all starts of width `≤ W` (death by time `n - 1`). -/
theorem q01_of_check (W n : Nat) (h : checkBelow n (2 ^ W) = true) (x : Nat → Bool) (hw : x 0 = false)
    (hx : FiniteW x W) : ∃ j, 2 * j < n ∧ run x (2 * j) 1 = false := by
  obtain ⟨r, hr, rfl⟩ := exists_pack W x hw hx
  obtain ⟨i, hi, hti, hpi⟩ := diesBy_sound n 0 r (checkBelow_sound n _ h r hr)
  refine ⟨i / 2, by omega, ?_⟩
  rw [show 2 * (i / 2) = i by omega, run_toFun]
  simp only [toFun]
  simp [hpi]

theorem check_16 : checkBelow 34 (2 ^ 16) = true := by decide +kernel

/-- **Q_01 for every start of width at most 16** (kernel-checked): every finitely supported configuration of
width `≤ 16` turns depth 1 white at some even time `< 34`. -/
theorem q01_width_le_16 (x : Nat → Bool) (hw : x 0 = false) (hx : FiniteW x 16) :
    ∃ j, 2 * j < 34 ∧ run x (2 * j) 1 = false :=
  q01_of_check 16 34 check_16 x hw hx

/-- The other phase: a start of width `≤ 15` cannot keep depth 1 black at every odd time. -/
theorem q01_width_le_15_odd (x : Nat → Bool) (hx : FiniteW x 15) :
    ∃ j, 2 * j < 34 ∧ run x (2 * j + 1) 1 = false := by
  obtain ⟨j, hj, h⟩ := q01_width_le_16 (step x) rfl (finite_step x 15 hx)
  refine ⟨j, hj, ?_⟩
  rw [show 2 * j + 1 = 1 + 2 * j by omega, run_add]; exact h

/-! ## Bridge to Rule 30 from a single black cell -/

section Bridge
open Ruliology.CellularAutomata.Rule30Jen

/-- The center column alternates from `T`: white at `T + 2j`, black at `T + 2j + 1`. -/
def Alt (T : Nat) : Prop := ∀ j : Nat, cell (T + 2 * j) 0 = false ∧ cell (T + 2 * j + 1) 0 = true

/-- The left half at time `T0` in mirrored coordinates (depth `k ≥ 1` is `cell T0 (-k)`), with a white wall. -/
def leftHalf (T0 : Nat) : Nat → Bool := fun k => if k = 0 then false else cell T0 (-(k : Int))

theorem alt_left_black {T : Nat} (h : Alt T) (j : Nat) : cell (T + 2 * j + 1) (-1) = true := by
  have e := cell_left (T + 2 * j + 1) 0
  rw [show (0 : Int) - 1 = -1 by rfl, show T + 2 * j + 1 + 1 = T + 2 * (j + 1) by omega,
    (h (j + 1)).1, (h j).2] at e
  rw [e]; rfl

/-- Effective boundary: once the center alternates, `cell t (-1) || cell t 0 = cell t (-1)`. -/
theorem alt_boundary {T : Nat} (h : Alt T) (t : Nat) (ht : T ≤ t) :
    (cell t (-1) || cell t 0) = cell t (-1) := by
  obtain ⟨j, hj⟩ : ∃ j, t = T + 2 * j ∨ t = T + 2 * j + 1 := ⟨(t - T) / 2, by omega⟩
  rcases hj with rfl | rfl
  · rw [(h j).1]; cases cell (T + 2 * j) (-1) <;> rfl
  · rw [alt_left_black h j]; rfl

/-- **The left half of an alternating Rule 30 evolves as the ZBL.** -/
theorem alt_left_run {T : Nat} (h : Alt T) (T0 : Nat) (hT0 : T ≤ T0) :
    ∀ t k, 1 ≤ k → run (leftHalf T0) t k = cell (T0 + t) (-(k : Int)) := by
  intro t
  induction t with
  | zero => intro k hk; simp [run_zero, leftHalf, show k ≠ 0 by omega]
  | succ t ih =>
    intro k hk
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [run_succ, step_succ, ih (k' + 2) (by omega), ih (k' + 1) (by omega),
      show T0 + (t + 1) = (T0 + t) + 1 by omega]
    show _ = rule (cell (T0 + t) (-((k' + 1 : Nat) : Int) - 1)) (cell (T0 + t) (-((k' + 1 : Nat) : Int)))
      (cell (T0 + t) (-((k' + 1 : Nat) : Int) + 1))
    rw [show -((k' + 1 : Nat) : Int) - 1 = -((k' + 2 : Nat) : Int) by omega]
    unfold rule
    cases k' with
    | zero =>
      rw [run_wall (by simp [leftHalf]) t, show -((0 + 1 : Nat) : Int) + 1 = 0 by omega,
        show ((0 + 1 : Nat) : Int) = 1 by rfl, alt_boundary h (T0 + t) (by omega)]
      simp
    | succ k'' =>
      rw [ih (k'' + 1) (by omega), show -((k'' + 1 + 1 : Nat) : Int) + 1 = -((k'' + 1 : Nat) : Int) by omega]

theorem leftHalf_finite (T0 : Nat) : FiniteW (leftHalf T0) T0 := by
  intro k hk
  simp only [leftHalf, show k ≠ 0 by omega, if_false]
  exact cell_eq_false_of_lt T0 _ (by omega)

/-- Under `Alt T`, the left half from time `T + 1` satisfies the phase-0 constraint forever. -/
theorem alt_constrained {T : Nat} (h : Alt T) (j : Nat) : run (leftHalf (T + 1)) (2 * j) 1 = true := by
  rw [alt_left_run h (T + 1) (by omega) (2 * j) 1 (by omega),
    show T + 1 + 2 * j = T + 2 * j + 1 by omega]
  exact alt_left_black h j

/-- **Parity of the first deviation from the stripe, for Rule 30 itself.** If the center column alternates from
`T`, then at every time `T + 1 + t` the first depth `d` at which the left half (cells `-1, -2, …`) deviates from the
stripe `…10101` satisfies `t + d` even: at the times where the center is black the first deviation is at an even
depth, at the times where it is white at an odd depth. -/
theorem alt_first_defect_parity {T : Nat} (h : Alt T) (t d : Nat) (hd : 1 ≤ d)
    (hag : ∀ k, 1 ≤ k → k < d → cell (T + 1 + t) (-(k : Int)) = s k)
    (hne : cell (T + 1 + t) (-(d : Int)) ≠ s d) : (t + d) % 2 = 0 := by
  apply first_defect_parity (leftHalf (T + 1)) (by simp [leftHalf]) (t + d) t d hd (by omega)
  · intro k hk1 hk2; rw [alt_left_run h (T + 1) (by omega) t k hk1]; exact hag k hk1 hk2
  · rw [alt_left_run h (T + 1) (by omega) t d hd]; exact hne
  · intro j _; exact alt_constrained h j

/-- Under `Alt T`, column `-1` of Rule 30 is not eventually periodic (Jen's argument through the ZBL). -/
theorem alt_col_neg1_aperiodic {T : Nat} (h : Alt T) :
    ¬ ∃ T' P, 1 ≤ P ∧ ∀ t, T' ≤ t → cell (t + P) (-1) = cell t (-1) := by
  rintro ⟨T', P, hP, hper⟩
  apply constrained_col1_aperiodic (leftHalf (T + 1)) (by simp [leftHalf]) (T + 1) (leftHalf_finite _)
    (alt_constrained h)
  refine ⟨T', P, hP, fun t ht => ?_⟩
  rw [alt_left_run h (T + 1) (by omega) _ 1 (by omega), alt_left_run h (T + 1) (by omega) _ 1 (by omega),
    show T + 1 + (t + P) = (T + 1 + t) + P by omega]
  exact hper _ (by omega)

/-- The kernel-checked finite case, transported: the center column cannot alternate from any `T ≤ 15`. -/
theorem not_alt_small (T : Nat) (hT : T ≤ 15) : ¬ Alt T := by
  intro h
  obtain ⟨j, _, hj⟩ := q01_width_le_16 (leftHalf (T + 1)) (by simp [leftHalf])
    (fun k hk => leftHalf_finite (T + 1) k (by omega))
  rw [alt_constrained h j] at hj; cases hj

end Bridge

end ZBL

-- writeup-r2 axiom audit (appended)
#print axioms ZBL.step_s
#print axioms ZBL.inv_step
#print axioms ZBL.first_defect_step
#print axioms ZBL.first_defect_run
#print axioms ZBL.first_defect_hits
#print axioms ZBL.first_defect_even
#print axioms ZBL.first_defect_parity
#print axioms ZBL.free_bit
#print axioms ZBL.reset_config
#print axioms ZBL.agrees_two_steps
#print axioms ZBL.agrees_run_even
#print axioms ZBL.agrees_pre
#print axioms ZBL.agrees_pre_run
#print axioms ZBL.finite_never_stripe
#print axioms ZBL.col1_not_eventually_true
#print axioms ZBL.all_columns_periodic
#print axioms ZBL.col1_periodic_white
#print axioms ZBL.constrained_col1_aperiodic
#print axioms ZBL.check_16
#print axioms ZBL.q01_width_le_16
#print axioms ZBL.q01_width_le_15_odd
#print axioms ZBL.alt_left_run
#print axioms ZBL.alt_constrained
#print axioms ZBL.alt_first_defect_parity
#print axioms ZBL.alt_col_neg1_aperiodic
#print axioms ZBL.not_alt_small
