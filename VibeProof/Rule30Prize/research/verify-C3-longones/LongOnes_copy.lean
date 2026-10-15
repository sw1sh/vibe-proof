import Ruliology.CellularAutomata.Rule30Prize

/-!
# Rule 30: the center column is not eventually periodic with a period word whose 1-runs are long

Scratch development (smallperiods agent, 2026-10-15).

* `absorb`: if the center column is black for 9 consecutive steps, then at the end of those
  steps column 1 is white and column 2 is black. (Finite check over the 2^11 possible contents of
  columns 1..11.)
* `effective_boundary`: `cell t (-1) || c t = cell t (-1) || (c t && c (t+1))` for every `t`,
  i.e. the left half only ever "sees" the center column through `c t && c (t + 1)`.
* `no_period_long_ones`: if the center column is eventually periodic and, from some point on,
  every maximal run of black center cells has length at least 9, then column 1 is forced at every
  white center cell, so column `-1` is eventually periodic too — contradicting Jen's theorem
  (`not_adjacent (-1)`). So no period word whose cyclic 1-runs all have length ≥ 9 can occur,
  whatever the transient.
-/

namespace R30SmallPeriods
open Ruliology.CellularAutomata.Rule30Jen
open Ruliology.CellularAutomata.Rule30Prize

/-! ### Evolving a finite window -/

/-- One rule-30 step on a window: `c` is the cell just left of the window, `l` the window (left to
right). The result holds the next values of every window cell except the last one. -/
def stepW (c : Bool) : List Bool → List Bool
  | [] => []
  | [_] => []
  | x :: y :: rest => rule c x y :: stepW x (y :: rest)

/-- The `n` cells at positions `a, a+1, …, a+n-1` at step `t`. -/
def win (t : Nat) (a : Int) : Nat → List Bool
  | 0 => []
  | n + 1 => cell t a :: win t (a + 1) n

theorem win_length (t : Nat) : ∀ (a : Int) (n : Nat), (win t a n).length = n
  | _, 0 => rfl
  | a, n + 1 => by simp [win, win_length t (a + 1) n]

theorem stepW_win (t : Nat) : ∀ (n : Nat) (a : Int),
    stepW (cell t (a - 1)) (win t a (n + 1)) = win (t + 1) a n
  | 0, a => by simp [win, stepW]
  | n + 1, a => by
    have ih := stepW_win t n (a + 1)
    rw [show a + 1 - 1 = a by omega] at ih
    show rule (cell t (a - 1)) (cell t a) (cell t (a + 1)) :: stepW (cell t a) (win t (a + 1) (n + 1))
      = cell (t + 1) a :: win (t + 1) (a + 1) n
    rw [ih]
    rfl

/-- `k` steps of the right half with a black center column. -/
def runTrue : Nat → List Bool → List Bool
  | 0, l => l
  | k + 1, l => runTrue k (stepW true l)

theorem runTrue_win : ∀ (k t n : Nat), (∀ i, i < k → cell (t + i) 0 = true) →
    runTrue k (win t 1 (n + k)) = win (t + k) 1 n
  | 0, t, n, _ => rfl
  | k + 1, t, n, h => by
    have h0 : cell t 0 = true := by simpa using h 0 (by omega)
    have hs : stepW true (win t 1 ((n + k) + 1)) = win (t + 1) 1 (n + k) := by
      have := stepW_win t (n + k) 1
      rw [show (1 : Int) - 1 = 0 by rfl, h0] at this
      exact this
    show runTrue k (stepW true (win t 1 ((n + k) + 1))) = win (t + (k + 1)) 1 n
    rw [hs, runTrue_win k (t + 1) n (fun i hi => by
      rw [show t + 1 + i = t + (i + 1) by omega]; exact h (i + 1) (by omega))]
    rw [show t + 1 + k = t + (k + 1) by omega]

/-- The finite check: 9 black center steps send every window `x₁ … x₁₁` to `(white, black)`. -/
theorem absorb_check : (allLists 11).all (fun l => runTrue 9 l == [false, true]) = true := by
  decide +kernel

/-- **Absorption.** Nine consecutive black center cells force column 1 white and column 2 black. -/
theorem absorb (t : Nat) (h : ∀ i, i < 9 → cell (t + i) 0 = true) :
    cell (t + 9) 1 = false ∧ cell (t + 9) 2 = true := by
  have hw := runTrue_win 9 t 2 h
  have hmem : win t 1 (2 + 9) ∈ allLists 11 := by
    have := mem_allLists (win t 1 (2 + 9))
    rwa [win_length] at this
  have hc := List.all_eq_true.1 absorb_check _ hmem
  rw [hw] at hc
  have : win (t + 9) 1 2 = [false, true] := by simpa using hc
  simp only [win] at this
  injection this with h1 h2
  injection h2 with h2 _
  exact ⟨h1, by simpa using h2⟩

/-- Once column 1 is white and column 2 black, a black center keeps them so. -/
theorem absorb_stay (t : Nat) (h1 : cell t 1 = false) (h2 : cell t 2 = true)
    (hc : cell t 0 = true) : cell (t + 1) 1 = false ∧ cell (t + 1) 2 = true := by
  constructor
  · show rule (cell t (1 - 1)) (cell t 1) (cell t (1 + 1)) = false
    rw [show (1 : Int) - 1 = 0 by rfl, hc, h1, show (1 : Int) + 1 = 2 by rfl, h2]; rfl
  · show rule (cell t (2 - 1)) (cell t 2) (cell t (2 + 1)) = true
    rw [show (2 : Int) - 1 = 1 by rfl, h1, h2]; rfl

/-! ### The effective boundary of the left half -/

/-- The left half sees the center column only through `c t && c (t + 1)`. -/
theorem effective_boundary (t : Nat) :
    (cell t (-1) || center t) = (cell t (-1) || (center t && center (t + 1))) := by
  have hl := cell_left t 0
  rw [show (0 : Int) - 1 = -1 by rfl] at hl
  unfold center
  rw [hl]
  cases cell (t + 1) 0 <;> cases cell t 0 <;> cases cell t (0 + 1) <;> rfl

/-- If the center is black and white next, column `-1` is black. -/
theorem left_of_black (t : Nat) (h : center t = true) :
    cell t (-1) = !center (t + 1) := by
  have hl := cell_left t 0
  rw [show (0 : Int) - 1 = -1 by rfl] at hl
  unfold center at h ⊢
  rw [hl, h]
  cases cell (t + 1) 0 <;> rfl

/-! ### Inside a white run of the center column -/

/-- During a white run of the center, once column 1 or column 2 is black, column 1 stays black. -/
theorem white_run (t : Nat) (h : (cell t 1 || cell t 2) = true) (hc : center t = false) :
    cell (t + 1) 1 = true := by
  show rule (cell t (1 - 1)) (cell t 1) (cell t (1 + 1)) = true
  unfold center at hc
  rw [show (1 : Int) - 1 = 0 by rfl, hc, show (1 : Int) + 1 = 2 by rfl]
  revert h; cases cell t 1 <;> cases cell t 2 <;> simp [rule]

/-! ### The main theorem -/

/-- Walk back from `t` to the first white cell of its white run (stopping at time `lo`). -/
def runStart (lo : Nat) : Nat → Nat
  | 0 => 0
  | t + 1 => if lo < t + 1 ∧ center t = false then runStart lo t else t + 1

theorem runStart_spec (lo : Nat) : ∀ t, lo ≤ t →
    lo ≤ runStart lo t ∧ runStart lo t ≤ t ∧
    (∀ j, runStart lo t ≤ j → j < t → center j = false) ∧
    (lo < runStart lo t → center (runStart lo t - 1) = true)
  | 0, h => by
    have : lo = 0 := by omega
    subst this
    refine ⟨Nat.le_refl _, by simp [runStart], fun j h1 h2 => by omega, fun h => by simp [runStart] at h⟩
  | t + 1, h => by
    by_cases hc : lo < t + 1 ∧ center t = false
    · have e : runStart lo (t + 1) = runStart lo t := by simp [runStart, hc]
      obtain ⟨a, b, c, d⟩ := runStart_spec lo t (by omega)
      rw [e]
      refine ⟨a, by omega, fun j h1 h2 => ?_, d⟩
      by_cases hj : j = t
      · subst hj; exact hc.2
      · exact c j h1 (by omega)
    · have e : runStart lo (t + 1) = t + 1 := by simp [runStart, hc]
      rw [e]
      refine ⟨h, Nat.le_refl _, fun j h1 h2 => by omega, fun h' => ?_⟩
      simp only [Nat.add_sub_cancel]
      cases hct : center t
      · exact absurd ⟨h', hct⟩ hc
      · rfl

/-- **No eventual period with long black runs.** If the center column has period `P` from `T` on,
and from `T + 9` on every white cell that follows a black cell is preceded by at least 9 black
cells, we reach a contradiction: either the center is eventually white (no column is eventually
constant), or column `-1` is eventually periodic alongside column `0` (Jen). -/
theorem no_period_long_ones (T P : Nat) (hP : 0 < P)
    (hper : ∀ t, T ≤ t → center (t + P) = center t)
    (hruns : ∀ t, T + 9 ≤ t → center t = false → center (t - 1) = true →
      ∀ i, i < 9 → center (t - 1 - i) = true) : False := by
  -- periodic shifts
  have hperk : ∀ k t, T ≤ t → center (t + k * P) = center t := by
    intro k; induction k with
    | zero => intro t _; simp
    | succ k ih => intro t ht; rw [show t + (k + 1) * P = (t + k * P) + P by
        rw [Nat.succ_mul]; omega, hper _ (by omega), ih t ht]
  -- Case: the center is eventually constant
  by_cases hone : ∃ u, T ≤ u ∧ u < T + P ∧ center u = true
  case neg =>
    apply center_not_eventually_constant
    refine ⟨T, false, fun t ht => ?_⟩
    have hq : t = (T + (t - T) % P) + ((t - T) / P) * P := by
      have := Nat.mod_add_div (t - T) P; rw [Nat.mul_comm] at this; omega
    rw [hq, hperk _ _ (by omega)]
    cases hc : center (T + (t - T) % P)
    · rfl
    · exact absurd ⟨_, by omega, by have := Nat.mod_lt (t - T) hP; omega, hc⟩ hone
  obtain ⟨u, hu1, hu2, hu⟩ := hone
  -- every window of length P after T contains a black cell
  have hwin : ∀ s, T ≤ s → ∃ v, s ≤ v ∧ v < s + P ∧ center v = true := by
    intro s hs
    -- v = u + k P for the right k
    have hdm := Nat.div_add_mod (s - u + P - 1) P
    have hml := Nat.mod_lt (s - u + P - 1) hP
    generalize (s - u + P - 1) / P = q at hdm ⊢
    generalize (s - u + P - 1) % P = r at hdm hml
    have hqp : q * P = P * q := Nat.mul_comm _ _
    have hq : q = 0 ∨ P ≤ q * P := by
      rcases Nat.eq_zero_or_pos q with h | h
      · exact Or.inl h
      · exact Or.inr (Nat.le_mul_of_pos_left P h)
    have hq0 : q = 0 → q * P = 0 := fun h => by rw [h]; exact Nat.zero_mul P
    refine ⟨u + q * P, by omega, by omega, ?_⟩
    rw [hperk _ _ hu1]; exact hu
  -- Key: for a white cell t ≥ T + 9 + P, column 1 at t is black iff the center at t-1 is white
  have key : ∀ t, T + 9 + P ≤ t → center t = false → cell t 1 = !center (t - 1) := by
    intro t ht hct
    obtain ⟨s0, s1, s2, s3⟩ := runStart_spec (T + 9) t (by omega)
    -- the run start is strictly after T + 9 (a black cell lies in [t - P, t - 1])
    obtain ⟨v, hv1, hv2, hv⟩ := hwin (t - P) (by omega)
    have hvt : v < t := by
      rcases Nat.lt_or_ge v t with h | h
      · exact h
      · have : v = t := by omega
        subst this; rw [hct] at hv; exact absurd hv (by simp)
    have hstart : T + 9 < runStart (T + 9) t := by
      rcases Nat.lt_or_ge (T + 9) (runStart (T + 9) t) with h | h
      · exact h
      · have := s2 v (by omega) hvt; rw [hv] at this; exact absurd this (by simp)
    have hprev := s3 hstart
    generalize hsdef : runStart (T + 9) t = s at s0 s1 s2 s3 hstart hprev
    -- s is white
    have hs_white : center s = false := by
      rcases Nat.lt_or_ge s t with h | h
      · exact s2 s (Nat.le_refl _) h
      · have : s = t := by omega
        rw [this]; exact hct
    -- absorption at the run start
    have hab := absorb (s - 9) (fun i hi => by
      have := hruns s (by omega) hs_white hprev (8 - i) (by omega)
      unfold center at this
      rw [show s - 1 - (8 - i) = s - 9 + i by omega] at this
      exact this)
    rw [show s - 9 + 9 = s by omega] at hab
    -- walk forward through the white run
    have walk : ∀ j, s < j → j ≤ t → cell j 1 = true := by
      intro j hj1 hj2
      induction j with
      | zero => omega
      | succ j ih =>
        apply white_run j
        · by_cases hjs : j = s
          · subst hjs; rw [hab.1, hab.2]; rfl
          · rw [ih (by omega) (by omega)]; rfl
        · rcases Nat.lt_or_ge j t with h | h
          · exact s2 j (by omega) h
          · omega
    rcases Nat.lt_or_ge s t with h | h
    · rw [walk t h (Nat.le_refl _)]
      have : center (t - 1) = false := s2 (t - 1) (by omega) (by omega)
      rw [this]; rfl
    · have : s = t := by omega
      rw [← this, hab.1, hprev]; rfl
  -- column -1 is eventually periodic
  have hleft : EventuallyPeriodic fun t => cell t (-1) := by
    refine ⟨T + 9 + P + 1, P, hP, fun t ht => ?_⟩
    have form : ∀ t, T + 9 + P + 1 ≤ t →
        cell t (-1) = xor (center (t + 1)) (center t || !center (t - 1)) := by
      intro t ht
      have hl := cell_left t 0
      rw [show (0 : Int) - 1 = -1 by rfl] at hl
      rw [hl]
      show xor (center (t + 1)) (center t || cell t (0 + 1)) = _
      cases hc : center t
      · rw [show (0 : Int) + 1 = 1 by rfl, key t (by omega) hc]
      · rfl
    simp only
    rw [form (t + P) (by omega), form t ht, show t + P + 1 = (t + 1) + P by omega,
      hper (t + 1) (by omega), hper t (by omega), show t + P - 1 = (t - 1) + P by omega,
      hper (t - 1) (by omega)]
  exact not_adjacent (-1) hleft (by
    exact ⟨T, P, hP, fun t ht => by
      show cell (t + P) (-1 + 1) = cell t (-1 + 1)
      rw [show (-1 : Int) + 1 = 0 by rfl]
      exact hper t ht⟩)

end R30SmallPeriods

#print axioms R30SmallPeriods.no_period_long_ones
#print axioms R30SmallPeriods.effective_boundary
#print axioms R30SmallPeriods.absorb
