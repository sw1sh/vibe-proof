import Ruliology.CellularAutomata.Rule30Jen

/-!
# Rule 30, driven left half: column `-1` encodes the state (barrier), and the `c ≡ 1` case

Scratch file (left-half / column-0 consistency angle).  Same driven-half definition as
`DrivenLeft.lean` (`L c s t p`, driver `c` at column `0`, start state `s` at time `0`).

* `light_cone`: column `-1` at step `k` depends only on the start cells `-1, …, -(k+1)`.
* `permutive`: if two starts agree on `-1, …, -k` and differ at `-(k+1)`, column `-1` differs at
  step `k` (the rightmost difference travels right at speed one).
* `exists_prefix`, `barrier_exists`, `barrier_unique`: **for every driver and every
  `b : Nat → Bool`, exactly one edge-structured start (leftmost black cell at `-n`, white beyond)
  has column `-1` equal to `b` on steps `0 … n-2`.**  So forced values of column `-1` on any
  window of length `n - 1` after the onset can always be met: a left-half argument must look at
  least `n - 1` steps past the onset (onset `T` ↔ `n = T`).
* `ones_fails`: for the driver `c ≡ 1` (forced values: column `-1` white at every step), every
  edge-structured start with edge at `-n` violates the forced values at some step `≤ n + 1`.
  This is a T-independent, left-half-only exclusion of the word `1`.
-/

namespace Ruliology.CellularAutomata
namespace Rule30DrivenLeftBarrier

open Rule30Jen

/-- The left half driven by the boundary column `c`, from left-half state `s` at time `0`. -/
def L (c : Nat → Bool) (s : Int → Bool) : Nat → Int → Bool
  | 0, p => if p < 0 then s p else c 0
  | t + 1, p => if p < 0 then rule (L c s t (p - 1)) (L c s t p) (L c s t (p + 1)) else c (t + 1)

variable {c : Nat → Bool}

theorem L_col0 (s : Int → Bool) (t : Nat) : L c s t 0 = c t := by
  cases t <;> simp [L]

theorem L_succ (s : Int → Bool) {t : Nat} {p : Int} (hp : p < 0) :
    L c s (t + 1) p = rule (L c s t (p - 1)) (L c s t p) (L c s t (p + 1)) := by
  simp [L, hp]

theorem L_zero (s : Int → Bool) {p : Int} (hp : p < 0) : L c s 0 p = s p := by
  simp [L, hp]

/-- Neighbour value: positions `p + 1 ≤ 0` agree if `p + 1 < 0` agrees or `p + 1 = 0` (driver). -/
theorem nb_agree {s s' : Int → Bool} {j : Nat} {p : Int} (hp : p < 0)
    (h : p + 1 < 0 → L c s j (p + 1) = L c s' j (p + 1)) : L c s j (p + 1) = L c s' j (p + 1) := by
  by_cases hq : p + 1 < 0
  · exact h hq
  · rw [show p + 1 = 0 by omega, L_col0, L_col0]

/-- **Light cone.** If two starts agree on `-(k+1) … -1`, then at step `j ≤ k` they agree on
`-(k+1-j) … -1`. -/
theorem light_cone {s s' : Int → Bool} {k : Nat}
    (h : ∀ p : Int, -((k + 1 : Nat) : Int) ≤ p → p < 0 → s p = s' p) :
    ∀ j : Nat, j ≤ k → ∀ p : Int, -((k + 1 - j : Nat) : Int) ≤ p → p < 0 →
      L c s j p = L c s' j p := by
  intro j
  induction j with
  | zero =>
    intro _ p hp1 hp2
    rw [L_zero s hp2, L_zero s' hp2]
    exact h p (by omega) hp2
  | succ j ih =>
    intro hj p hp1 hp2
    rw [L_succ s hp2, L_succ s' hp2, ih (by omega) (p - 1) (by omega) (by omega),
      ih (by omega) p (by omega) hp2,
      nb_agree hp2 (fun hq => ih (by omega) (p + 1) (by omega) hq)]

theorem rule_not (a b d : Bool) : rule (!a) b d = !rule a b d := by
  cases a <;> cases b <;> cases d <;> rfl

/-- **Permutivity.** If two starts agree on `-k … -1` and differ at `-(k+1)`, then at step `j ≤ k`
they agree on `-(k-j) … -1` and differ at `-(k+1-j)`. -/
theorem permutive_aux {s s' : Int → Bool} {k : Nat}
    (hag : ∀ p : Int, -((k : Nat) : Int) ≤ p → p < 0 → s p = s' p)
    (hd : s (-((k + 1 : Nat) : Int)) = !s' (-((k + 1 : Nat) : Int))) :
    ∀ j : Nat, j ≤ k → (∀ p : Int, -((k - j : Nat) : Int) ≤ p → p < 0 → L c s j p = L c s' j p) ∧
      L c s j (-((k + 1 - j : Nat) : Int)) = !L c s' j (-((k + 1 - j : Nat) : Int)) := by
  intro j
  induction j with
  | zero =>
    intro _
    refine ⟨fun p hp1 hp2 => ?_, ?_⟩
    · rw [L_zero s hp2, L_zero s' hp2]; exact hag p (by omega) hp2
    · rw [L_zero s (by omega), L_zero s' (by omega)]; simpa using hd
  | succ j ih =>
    intro hj
    have ih' := ih (by omega)
    refine ⟨fun p hp1 hp2 => ?_, ?_⟩
    · rw [L_succ s hp2, L_succ s' hp2, ih'.1 (p - 1) (by omega) (by omega), ih'.1 p (by omega) hp2,
        nb_agree hp2 (fun hq => ih'.1 (p + 1) (by omega) hq)]
    · have hp2 : -((k + 1 - (j + 1) : Nat) : Int) < 0 := by omega
      rw [L_succ s hp2, L_succ s' hp2,
        show -((k + 1 - (j + 1) : Nat) : Int) - 1 = -((k + 1 - j : Nat) : Int) by omega, ih'.2,
        ih'.1 (-((k + 1 - (j + 1) : Nat) : Int)) (by omega) hp2,
        nb_agree hp2 (fun hq => ih'.1 _ (by omega) hq), rule_not]

theorem permutive {s s' : Int → Bool} {k : Nat}
    (hag : ∀ p : Int, -((k : Nat) : Int) ≤ p → p < 0 → s p = s' p)
    (hd : s (-((k + 1 : Nat) : Int)) = !s' (-((k + 1 : Nat) : Int))) :
    L c s k (-1) = !L c s' k (-1) := by
  have := (permutive_aux (c := c) hag hd k (Nat.le_refl k)).2
  rwa [show -((k + 1 - k : Nat) : Int) = -1 by omega] at this

/-- Any prefix of column `-1` of length `j` is produced by some start supported on `-j … -1`. -/
theorem exists_prefix (b : Nat → Bool) : ∀ j : Nat, ∃ s : Int → Bool,
    (∀ p : Int, p < -((j : Nat) : Int) → s p = false) ∧ ∀ k, k < j → L c s k (-1) = b k := by
  intro j
  induction j with
  | zero => exact ⟨fun _ => false, fun _ _ => rfl, fun k hk => absurd hk (Nat.not_lt_zero k)⟩
  | succ j ih =>
    obtain ⟨s, hsupp, hpre⟩ := ih
    let v : Bool := xor (L c s j (-1)) (b j)
    let s' : Int → Bool := fun p => if p = -((j + 1 : Nat) : Int) then v else s p
    have hagree : ∀ p : Int, -((j : Nat) : Int) ≤ p → p < 0 → s' p = s p := by
      intro p hp1 _
      simp only [s']
      rw [if_neg (by omega)]
    refine ⟨s', fun p hp => ?_, fun k hk => ?_⟩
    · simp only [s']
      rw [if_neg (by omega)]
      exact hsupp p (by omega)
    · by_cases hkj : k < j
      · rw [← hpre k hkj]
        exact light_cone (k := k) (fun p hp1 hp2 => hagree p (by omega) hp2) k (Nat.le_refl k) (-1)
          (by omega) (by omega)
      · have hk' : k = j := by omega
        subst hk'
        have hsj : s (-((k + 1 : Nat) : Int)) = false := hsupp _ (by omega)
        have hs'j : s' (-((k + 1 : Nat) : Int)) = v := by simp [s']
        cases hv : v
        · -- `s'` equals `s` on `-(k+1) … -1`
          have heq : L c s' k (-1) = L c s k (-1) :=
            light_cone (k := k) (fun p hp1 hp2 => by
              by_cases e : p = -((k + 1 : Nat) : Int)
              · rw [e, hs'j, hsj, hv]
              · exact hagree p (by omega) hp2) k (Nat.le_refl k) (-1) (by omega) (by omega)
          rw [heq]
          have : xor (L c s k (-1)) (b k) = false := hv
          revert this; cases L c s k (-1) <;> cases b k <;> simp
        · -- `s'` differs from `s` exactly at `-(k+1)`
          have hp := permutive (c := c) (k := k) (s := s') (s' := s) (fun p hp1 hp2 => hagree p hp1 hp2)
            (by rw [hs'j, hsj, hv]; rfl)
          rw [hp]
          have : xor (L c s k (-1)) (b k) = true := hv
          revert this; cases L c s k (-1) <;> cases b k <;> simp

/-- **Barrier (existence).** For every driver, every `n ≥ 1` and every `b`, some start with its
leftmost black cell at `-n` (white beyond) has column `-1` equal to `b` at steps `0 … n-2`. -/
theorem barrier_exists (b : Nat → Bool) {n : Nat} (hn : 0 < n) : ∃ s : Int → Bool,
    (∀ p : Int, p < -((n : Nat) : Int) → s p = false) ∧ s (-((n : Nat) : Int)) = true ∧
      ∀ k, k + 1 < n → L c s k (-1) = b k := by
  obtain ⟨s, hsupp, hpre⟩ := exists_prefix (c := c) b (n - 1)
  let s' : Int → Bool := fun p => if p = -((n : Nat) : Int) then true else s p
  refine ⟨s', fun p hp => ?_, by simp [s'], fun k hk => ?_⟩
  · simp only [s']
    rw [if_neg (by omega)]
    exact hsupp p (by omega)
  · rw [← hpre k (by omega)]
    exact light_cone (k := k) (fun p hp1 hp2 => by simp only [s']; rw [if_neg (by omega)])
      k (Nat.le_refl k) (-1) (by omega) (by omega)

/-- **Barrier (uniqueness).** Two starts with leftmost black cell at `-n` (white beyond) whose
columns `-1` agree at steps `0 … n-2` are equal. -/
theorem barrier_unique {s s' : Int → Bool} {n : Nat}
    (hs0 : ∀ p : Int, p < -((n : Nat) : Int) → s p = false) (hs1 : s (-((n : Nat) : Int)) = true)
    (hs0' : ∀ p : Int, p < -((n : Nat) : Int) → s' p = false) (hs1' : s' (-((n : Nat) : Int)) = true)
    (hx : ∀ k, k + 1 < n → L c s k (-1) = L c s' k (-1)) :
    ∀ p : Int, p < 0 → s p = s' p := by
  -- agreement on `-k … -1` for all `k ≤ n - 1`, by induction
  have key : ∀ k : Nat, k + 1 ≤ n → ∀ p : Int, -((k : Nat) : Int) ≤ p → p < 0 → s p = s' p := by
    intro k
    induction k with
    | zero => intro _ p hp1 hp2; omega
    | succ k ih =>
      intro hk p hp1 hp2
      by_cases e : p = -((k + 1 : Nat) : Int)
      · subst e
        cases h1 : s (-((k + 1 : Nat) : Int)) <;> cases h2 : s' (-((k + 1 : Nat) : Int))
        · rfl
        · exact absurd (hx k (by omega)) (by
            rw [permutive (c := c) (ih (by omega)) (by rw [h1, h2]; rfl)]
            cases L c s' k (-1) <;> simp)
        · exact absurd (hx k (by omega)) (by
            rw [permutive (c := c) (ih (by omega)) (by rw [h1, h2]; rfl)]
            cases L c s' k (-1) <;> simp)
        · rfl
      · exact ih (by omega) p (by omega) hp2
  intro p hp
  by_cases h1 : p < -((n : Nat) : Int)
  · rw [hs0 p h1, hs0' p h1]
  by_cases h2 : p = -((n : Nat) : Int)
  · rw [h2, hs1, hs1']
  · exact key (n - 1) (by omega) p (by omega) hp

/-! ### The word `1`: a T-independent left-only exclusion -/

/-- The alternating half-configuration: black exactly at even positions. -/
def alt (p : Int) : Bool := decide (p % 2 = 0)

theorem alt_fixed : ∀ t : Nat, ∀ p : Int, p < 0 → L (fun _ => true) alt t p = alt p := by
  intro t
  induction t with
  | zero => intro p hp; exact L_zero alt hp
  | succ t ih =>
    intro p hp
    rw [L_succ alt hp, ih (p - 1) (by omega), ih p hp]
    have hr : L (fun _ => true) alt t (p + 1) = alt (p + 1) := by
      by_cases hq : p + 1 < 0
      · exact ih (p + 1) hq
      · rw [show p + 1 = 0 by omega, L_col0]; rfl
    rw [hr]
    simp only [alt, rule]
    have : p % 2 = 0 ∨ p % 2 = 1 := by omega
    rcases this with h | h
    · have h1 : (p - 1) % 2 = 1 := by omega
      simp [h, h1]
    · have h1 : (p - 1) % 2 = 0 := by omega
      have h2 : (p + 1) % 2 = 0 := by omega
      simp [h, h1, h2]

/-- **The word `1` is excluded by the left half alone, uniformly in the onset.** With driver
`c ≡ 1`, the forced values say column `-1` is white at every step; every start whose leftmost black
cell is at `-n` (white beyond) violates this at some step `k ≤ n + 1`. -/
theorem ones_fails {s : Int → Bool} {n : Nat} (hn : 0 < n)
    (hs0 : ∀ p : Int, p < -((n : Nat) : Int) → s p = false) (hs1 : s (-((n : Nat) : Int)) = true) :
    ∃ k, k ≤ n + 1 ∧ L (fun _ => true) s k (-1) = true := by
  refine Classical.byContradiction fun hno => ?_
  have hx : ∀ k, k ≤ n + 1 → L (fun _ => true) s k (-1) = false := by
    intro k hk
    cases h : L (fun _ => true) s k (-1)
    · rfl
    · exact absurd ⟨k, hk, h⟩ hno
  -- `s` agrees with `alt` on `-k … -1` for all `k ≤ n + 2`
  have key : ∀ k : Nat, k ≤ n + 2 → ∀ p : Int, -((k : Nat) : Int) ≤ p → p < 0 → s p = alt p := by
    intro k
    induction k with
    | zero => intro _ p hp1 hp2; omega
    | succ k ih =>
      intro hk p hp1 hp2
      by_cases e : p = -((k + 1 : Nat) : Int)
      · subst e
        cases h1 : s (-((k + 1 : Nat) : Int)) <;> cases h2 : alt (-((k + 1 : Nat) : Int))
        · rfl
        · have hp := permutive (c := fun _ => true) (k := k) (s := s) (s' := alt) (ih (by omega))
            (by rw [h1, h2]; rfl)
          rw [hx k (by omega), alt_fixed k (-1) (by omega)] at hp
          exact absurd hp (by decide)
        · have hp := permutive (c := fun _ => true) (k := k) (s := s) (s' := alt) (ih (by omega))
            (by rw [h1, h2]; rfl)
          rw [hx k (by omega), alt_fixed k (-1) (by omega)] at hp
          exact absurd hp (by decide)
        · rfl
      · exact ih (by omega) p (by omega) hp2
  have e1 := key (n + 2) (Nat.le_refl _) (-((n : Nat) : Int)) (by omega) (by omega)
  have e2 := key (n + 2) (Nat.le_refl _) (-((n : Nat) : Int) - 2) (by omega) (by omega)
  rw [hs1] at e1
  rw [hs0 _ (by omega)] at e2
  simp only [alt] at e1 e2
  have h1 : -((n : Nat) : Int) % 2 = 0 := by simpa using e1.symm
  have h2 : ¬ ((-((n : Nat) : Int) - 2) % 2 = 0) := by simpa using e2.symm
  omega

end Rule30DrivenLeftBarrier
end Ruliology.CellularAutomata

/-! ## Verifier addition: a left-only exclusion of the word `1` that uses only times `≤ 2T - 2`

Uses, besides the driven left half and the column-0 forced constraints, two T-uniform facts about
the real left half near its edge: the left diagonals `D₂ ≡ 0` and `D₄ ≡ 1`
(`D_j t = cell t (j - t)`). No right-half cell is used. -/

namespace Ruliology.CellularAutomata
namespace Rule30WordOneEarly

open Rule30Jen Rule30DrivenLeftBarrier

/-- `D₁ ≡ 1` (from time 1). -/
theorem d1 (t : Nat) : cell (t + 1) (-(t : Int)) = true := by
  show rule (cell t (-(t : Int) - 1)) (cell t (-(t : Int))) (cell t (-(t : Int) + 1)) = true
  rw [cell_eq_false_of_lt t _ (by omega), cell_left_edge t]
  rfl

/-- `D₂ ≡ 0` (from time 2). -/
theorem d2 (t : Nat) : cell (t + 2) (-(t : Int)) = false := by
  show rule (cell (t + 1) (-(t : Int) - 1)) (cell (t + 1) (-(t : Int)))
    (cell (t + 1) (-(t : Int) + 1)) = false
  rw [show -(t : Int) - 1 = -((t + 1 : Nat) : Int) by omega, cell_left_edge (t + 1), d1 t]
  rfl

/-- `D₄ ≡ 1` (from time 4). -/
theorem d4 : ∀ t : Nat, cell (t + 4) (-(t : Int)) = true := by
  intro t
  induction t with
  | zero => decide
  | succ t ih =>
    rw [show t + 1 + 4 = (t + 4) + 1 by omega]
    have h2 : cell (t + 4) (-((t + 1 : Nat) : Int) - 1) = false := by
      have := d2 (t + 2)
      rw [show t + 2 + 2 = t + 4 by omega,
        show -((t + 2 : Nat) : Int) = -((t + 1 : Nat) : Int) - 1 by omega] at this
      exact this
    have h4 : cell (t + 4) (-((t + 1 : Nat) : Int) + 1) = true := by
      rw [show -((t + 1 : Nat) : Int) + 1 = -(t : Int) by omega]; exact ih
    show rule (cell (t + 4) (-((t + 1 : Nat) : Int) - 1)) (cell (t + 4) (-((t + 1 : Nat) : Int)))
      (cell (t + 4) (-((t + 1 : Nat) : Int) + 1)) = true
    rw [h2, h4]
    cases cell (t + 4) (-((t + 1 : Nat) : Int)) <;> rfl

/-- Column `-1` up to step `k` only sees the driver at steps `< k`. -/
theorem driver_cone (s : Int → Bool) {c c' : Nat → Bool} :
    ∀ k : Nat, (∀ j, j < k → c j = c' j) → ∀ p : Int, p < 0 → L c s k p = L c' s k p := by
  intro k
  induction k with
  | zero => intro _ p hp; rw [L_zero s hp, L_zero s hp]
  | succ k ih =>
    intro h p hp
    have ih' := ih (fun j hj => h j (by omega))
    rw [L_succ s hp, L_succ s hp, ih' (p - 1) (by omega), ih' p hp]
    by_cases hq : p + 1 < 0
    · rw [ih' (p + 1) hq]
    · rw [show p + 1 = 0 by omega, L_col0, L_col0, h k (by omega)]

/-- The real left half from time `T` on is the driven left half (same proof as `DrivenLeft`). -/
theorem cell_eq_L (T : Nat) : ∀ k : Nat, ∀ p : Int, p ≤ 0 →
    L (fun k => cell (T + k) 0) (fun p => cell T p) k p = cell (T + k) p := by
  intro k
  induction k with
  | zero =>
    intro p hp
    by_cases h : p < 0
    · rw [L_zero _ h]; rfl
    · rw [show p = 0 by omega, L_col0]
  | succ k ih =>
    intro p hp
    by_cases h : p < 0
    · rw [L_succ _ h, ih (p - 1) (by omega), ih p (by omega), ih (p + 1) (by omega)]
      rfl
    · rw [show p = 0 by omega, L_col0]

/-- Word-`1` forced values on steps `0 … K` force agreement with `alt` on `-1 … -(K+1)`. -/
theorem agree_alt {s : Int → Bool} {K : Nat}
    (hx : ∀ k, k ≤ K → L (fun _ => true) s k (-1) = false) :
    ∀ k : Nat, k ≤ K + 1 → ∀ p : Int, -((k : Nat) : Int) ≤ p → p < 0 → s p = alt p := by
  intro k
  induction k with
  | zero => intro _ p hp1 hp2; omega
  | succ k ih =>
    intro hk p hp1 hp2
    by_cases e : p = -((k + 1 : Nat) : Int)
    · subst e
      cases h1 : s (-((k + 1 : Nat) : Int)) <;> cases h2 : alt (-((k + 1 : Nat) : Int))
      · rfl
      · have hp := permutive (c := fun _ => true) (k := k) (s := s) (s' := alt) (ih (by omega))
          (by rw [h1, h2]; rfl)
        rw [hx k (by omega), alt_fixed k (-1) (by omega)] at hp
        exact absurd hp (by decide)
      · have hp := permutive (c := fun _ => true) (k := k) (s := s) (s' := alt) (ih (by omega))
          (by rw [h1, h2]; rfl)
        rw [hx k (by omega), alt_fixed k (-1) (by omega)] at hp
        exact absurd hp (by decide)
      · rfl
    · exact ih (by omega) p (by omega) hp2

/-- **Abstract (driven-system) form.** No left-half state with `s (-(T-2)) = 0` and
`s (-(T-4)) = 1` meets the word-`1` forced values (column `-1` white) at steps `0 … T-3`. -/
theorem word_one_early {s : Int → Bool} {T : Nat} (hT : 5 ≤ T)
    (h2 : s (-((T - 2 : Nat) : Int)) = false) (h4 : s (-((T - 4 : Nat) : Int)) = true) :
    ∃ k, k ≤ T - 3 ∧ L (fun _ => true) s k (-1) = true := by
  refine Classical.byContradiction fun hno => ?_
  have hx : ∀ k, k ≤ T - 3 → L (fun _ => true) s k (-1) = false := by
    intro k hk
    cases h : L (fun _ => true) s k (-1)
    · rfl
    · exact absurd ⟨k, hk, h⟩ hno
  have key := agree_alt hx
  have e2 := key (T - 2) (by omega) (-((T - 2 : Nat) : Int)) (by omega) (by omega)
  have e4 := key (T - 2) (by omega) (-((T - 4 : Nat) : Int)) (by omega) (by omega)
  rw [h2] at e2
  rw [h4] at e4
  simp only [alt] at e2 e4
  have a2 : ¬ (-((T - 2 : Nat) : Int) % 2 = 0) := by simpa using e2.symm
  have a4 : -((T - 4 : Nat) : Int) % 2 = 0 := by simpa using e4.symm
  omega

/-- **The word `1` is excluded inside the window `[T, 2T-2]`, for every onset `T ≥ 5`,** using only
the forced values of column `-1` at times `T … 2T-3`, the driven left half, and `D₂(T) = 0`,
`D₄(T) = 1`. (Onsets can always be increased, so `T ≥ 5` is no restriction.) -/
theorem word_one_window (T : Nat) (hT : 5 ≤ T)
    (hc : ∀ t, T ≤ t → t ≤ 2 * T - 2 → cell t 0 = true) : False := by
  -- forced constraints (column-0 consistency where the center is black)
  have hforced : ∀ k, k ≤ T - 3 → cell (T + k) (-1) = false := by
    intro k hk
    have h := cell_left (T + k) 0
    rw [show (0 : Int) - 1 = -1 by omega, hc (T + k + 1) (by omega) (by omega),
      hc (T + k) (by omega) (by omega)] at h
    rw [h]; rfl
  have hs2 : cell T (-((T - 2 : Nat) : Int)) = false := by
    have := d2 (T - 2); rwa [show T - 2 + 2 = T by omega] at this
  have hs4 : cell T (-((T - 4 : Nat) : Int)) = true := by
    have := d4 (T - 4); rwa [show T - 4 + 4 = T by omega] at this
  obtain ⟨k, hk, hk1⟩ := word_one_early (s := fun p => cell T p) hT hs2 hs4
  rw [driver_cone (fun p => cell T p) (c' := fun k => cell (T + k) 0) k
      (fun j hj => (hc (T + j) (by omega) (by omega)).symm) (-1) (by omega),
    cell_eq_L T k (-1) (by omega), hforced k hk] at hk1
  exact absurd hk1 (by decide)

end Rule30WordOneEarly
end Ruliology.CellularAutomata

#print axioms Ruliology.CellularAutomata.Rule30WordOneEarly.word_one_early
#print axioms Ruliology.CellularAutomata.Rule30WordOneEarly.word_one_window
