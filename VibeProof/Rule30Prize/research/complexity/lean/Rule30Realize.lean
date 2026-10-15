import Ruliology.CellularAutomata.Rule30Jen

/-!
# Every column sequence is realized, with any prescribed right half (scratch)

For rule 30 on the full line, fix the cells at positions `p ≥ 1` arbitrarily (`R`) and fix any
target sequence `c : Nat → Bool` for column `0`. Then there is exactly one way to fill the
positions `p ≤ 0` so that column `0` of the evolution is `c`.

Consequence: no argument that ignores the left half's left-finiteness can show that a column
is aperiodic. In particular, for every periodic `c` and every right half, there is a
configuration whose column `0` is `c`; by uniqueness its left half is the one forced below,
and it is not the single seed's (Problem 1 says so; Jen-type arguments must use the left edge).
-/

namespace R30Realize
open Ruliology.CellularAutomata.Rule30Jen

/-- Rule 30 from an arbitrary configuration. -/
def evol (x : Int → Bool) : Nat → Int → Bool
  | 0, p => x p
  | t + 1, p => rule (evol x t (p - 1)) (evol x t p) (evol x t (p + 1))

/-- The right half (positions `≥ 1`) driven at position `0` by the column `c`. -/
def rh (R : Int → Bool) (c : Nat → Bool) : Nat → Int → Bool
  | 0, p => R p
  | t + 1, p => rule (if p = 1 then c t else rh R c t (p - 1)) (rh R c t p) (rh R c t (p + 1))

/-- Column `-1`, forced by the requirement that column `0` follows `c`. -/
def ycol (R : Int → Bool) (c : Nat → Bool) (t : Nat) : Bool :=
  xor (c (t + 1)) (c t || rh R c t 1)

/-- `lc m t`: the column at position `-m`, rebuilt leftwards by left-permutivity. -/
def lc (R : Int → Bool) (c : Nat → Bool) : Nat → Nat → Bool
  | 0, t => c t
  | 1, t => ycol R c t
  | m + 2, t => xor (lc R c (m + 1) (t + 1)) (lc R c (m + 1) t || lc R c m t)

/-- The configuration: `R` on the right, the rebuilt left half at time `0` on the left. -/
def conf (R : Int → Bool) (c : Nat → Bool) (p : Int) : Bool :=
  if 1 ≤ p then R p else lc R c (-p).toNat 0

theorem xor_xor_cancel (a b : Bool) : xor (xor a b) b = a := by
  cases a <;> cases b <;> rfl

theorem lc_step (R : Int → Bool) (c : Nat → Bool) (m t : Nat) :
    rule (lc R c (m + 2) t) (lc R c (m + 1) t) (lc R c m t) = lc R c (m + 1) (t + 1) := by
  show xor (xor (lc R c (m + 1) (t + 1)) (lc R c (m + 1) t || lc R c m t))
    (lc R c (m + 1) t || lc R c m t) = _
  exact xor_xor_cancel _ _

theorem center_step (R : Int → Bool) (c : Nat → Bool) (t : Nat) :
    rule (lc R c 1 t) (lc R c 0 t) (rh R c t 1) = lc R c 0 (t + 1) := by
  show xor (xor (c (t + 1)) (c t || rh R c t 1)) (c t || rh R c t 1) = c (t + 1)
  exact xor_xor_cancel _ _

/-- **The evolution of `conf R c`**: on the right it is the driven right half, on the left
(including column `0`) it is the rebuilt left columns. -/
theorem evol_conf (R : Int → Bool) (c : Nat → Bool) : ∀ t p,
    evol (conf R c) t p = if 1 ≤ p then rh R c t p else lc R c (-p).toNat t
  | 0, p => by
    simp only [evol, conf]
    by_cases h : 1 ≤ p
    · rw [if_pos h, if_pos h]; rfl
    · rw [if_neg h, if_neg h]
  | t + 1, p => by
    have ih := evol_conf R c t
    show rule (evol (conf R c) t (p - 1)) (evol (conf R c) t p) (evol (conf R c) t (p + 1)) = _
    rw [ih (p - 1), ih p, ih (p + 1)]
    by_cases h1 : 1 ≤ p
    · have e1 : (if 1 ≤ p then rh R c (t + 1) p else lc R c (-p).toNat (t + 1)) = rh R c (t + 1) p :=
        if_pos h1
      have e2 : (if 1 ≤ p then rh R c t p else lc R c (-p).toNat t) = rh R c t p := if_pos h1
      have e3 : (if 1 ≤ p + 1 then rh R c t (p + 1) else lc R c (-(p + 1)).toNat t) = rh R c t (p + 1) :=
        if_pos (by omega)
      rw [e1, e2, e3]
      show _ = rule (if p = 1 then c t else rh R c t (p - 1)) (rh R c t p) (rh R c t (p + 1))
      by_cases h2 : p = 1
      · subst h2
        rw [if_neg (by decide), if_pos rfl]
        rfl
      · rw [if_pos (show 1 ≤ p - 1 by omega), if_neg h2]
    · have e1 : (if 1 ≤ p then rh R c (t + 1) p else lc R c (-p).toNat (t + 1)) = lc R c (-p).toNat (t + 1) :=
        if_neg h1
      have e2 : (if 1 ≤ p then rh R c t p else lc R c (-p).toNat t) = lc R c (-p).toNat t := if_neg h1
      have e4 : (if 1 ≤ p - 1 then rh R c t (p - 1) else lc R c (-(p - 1)).toNat t) =
          lc R c (-(p - 1)).toNat t := if_neg (by omega)
      rw [e1, e2, e4]
      by_cases h0 : p = 0
      · subst h0
        rw [if_pos (by decide)]
        exact center_step R c t
      · -- p ≤ -1: write -p = m + 1
        obtain ⟨m, hm⟩ : ∃ m : Nat, (-p).toNat = m + 1 := ⟨(-p).toNat - 1, by omega⟩
        rw [if_neg (show ¬ 1 ≤ p + 1 by omega), hm,
          show (-(p - 1)).toNat = m + 2 by omega, show (-(p + 1)).toNat = m by omega]
        exact lc_step R c m t

/-- **Realization**: for every right half `R` and every target column `c`, the configuration
`conf R c` agrees with `R` on positions `≥ 1` and its column `0` is exactly `c`. -/
theorem realize (R : Int → Bool) (c : Nat → Bool) :
    (∀ p, 1 ≤ p → conf R c p = R p) ∧ ∀ t, evol (conf R c) t 0 = c t := by
  refine ⟨fun p hp => by simp [conf, hp], fun t => ?_⟩
  rw [evol_conf R c t 0, if_neg (by decide)]
  rfl

/-! ### Uniqueness: the left half is determined by the right half and column `0` -/

/-- Rule 30 can be solved for the left cell. -/
theorem rule_left (a b d : Bool) : a = xor (rule a b d) (b || d) := by
  cases a <;> cases b <;> cases d <;> rfl

/-- If two configurations agree on positions `≥ 1` and have the same column `0`, their right
halves agree at all times. -/
theorem right_agree {x x' : Int → Bool} (hR : ∀ p, 1 ≤ p → x p = x' p)
    (h0 : ∀ t, evol x t 0 = evol x' t 0) : ∀ t p, 0 ≤ p → evol x t p = evol x' t p
  | 0, p, hp => by
    by_cases h : p = 0
    · subst h; exact h0 0
    · exact hR p (by omega)
  | t + 1, p, hp => by
    by_cases h : p = 0
    · subst h; exact h0 (t + 1)
    · show rule (evol x t (p - 1)) (evol x t p) (evol x t (p + 1)) =
        rule (evol x' t (p - 1)) (evol x' t p) (evol x' t (p + 1))
      rw [right_agree hR h0 t (p - 1) (by omega), right_agree hR h0 t p hp,
        right_agree hR h0 t (p + 1) (by omega)]

/-- Then the left halves agree too, column by column (left-permutivity). -/
theorem left_agree {x x' : Int → Bool} (hR : ∀ p, 1 ≤ p → x p = x' p)
    (h0 : ∀ t, evol x t 0 = evol x' t 0) :
    ∀ m : Nat, ∀ t, evol x t (-(m : Int)) = evol x' t (-(m : Int)) ∧
      evol x t (-(m : Int) + 1) = evol x' t (-(m : Int) + 1)
  | 0, t => ⟨by simpa using h0 t, right_agree hR h0 t _ (by omega)⟩
  | m + 1, t => by
    have ih := left_agree hR h0 m
    refine ⟨?_, ?_⟩
    · have e : ∀ y : Int → Bool, evol y t (-((m + 1 : Nat) : Int)) =
          xor (evol y (t + 1) (-(m : Int))) (evol y t (-(m : Int)) || evol y t (-(m : Int) + 1)) := by
        intro y
        have := rule_left (evol y t (-((m + 1 : Nat) : Int))) (evol y t (-(m : Int)))
          (evol y t (-(m : Int) + 1))
        rw [this]
        show xor (rule _ _ _) _ = xor (rule (evol y t (-(m : Int) - 1)) _ _) _
        rw [show -(m : Int) - 1 = -((m + 1 : Nat) : Int) by omega]
      rw [e x, e x', (ih (t + 1)).1, (ih t).1, (ih t).2]
    · rw [show -((m + 1 : Nat) : Int) + 1 = -(m : Int) by omega]
      exact (ih t).1

/-- **Uniqueness**: a configuration is determined by its right half and its column `0`. -/
theorem unique {x x' : Int → Bool} (hR : ∀ p, 1 ≤ p → x p = x' p)
    (h0 : ∀ t, evol x t 0 = evol x' t 0) : x = x' := by
  funext p
  by_cases hp : 0 ≤ p
  · exact right_agree hR h0 0 p hp
  · have := (left_agree hR h0 (-p).toNat 0).1
    rwa [show -(((-p).toNat : Nat) : Int) = p by omega] at this

/-- **Every eventually periodic column is realizable with any right half**: so a proof that a
column is aperiodic must use the left half (for the single seed: its left edge). -/
theorem column_realizable_unique (R : Int → Bool) (c : Nat → Bool) :
    ∃ x : Int → Bool, (∀ p, 1 ≤ p → x p = R p) ∧ (∀ t, evol x t 0 = c t) ∧
      ∀ x' : Int → Bool, (∀ p, 1 ≤ p → x' p = R p) → (∀ t, evol x' t 0 = c t) → x' = x :=
  ⟨conf R c, (realize R c).1, (realize R c).2, fun _ h1 h2 =>
    unique (fun p hp => (h1 p hp).trans ((realize R c).1 p hp).symm)
      (fun t => (h2 t).trans ((realize R c).2 t).symm)⟩

/-! ### Finite dependence, and the single seed -/

/-- The driven right half up to time `t` only sees `c` before `t`. -/
theorem rh_congr (R : Int → Bool) {c c' : Nat → Bool} :
    ∀ t, (∀ s, s < t → c s = c' s) → ∀ p, rh R c t p = rh R c' t p
  | 0, _, p => rfl
  | t + 1, h, p => by
    show rule (if p = 1 then c t else rh R c t (p - 1)) (rh R c t p) (rh R c t (p + 1)) =
      rule (if p = 1 then c' t else rh R c' t (p - 1)) (rh R c' t p) (rh R c' t (p + 1))
    have ih := rh_congr R t (fun s hs => h s (by omega))
    rw [ih (p - 1), ih p, ih (p + 1), h t (by omega)]

/-- The rebuilt column `-m` at time `t` only sees `c` up to time `m + t`. -/
theorem lc_congr (R : Int → Bool) {c c' : Nat → Bool} :
    ∀ m t, (∀ s, s ≤ m + t → c s = c' s) → lc R c m t = lc R c' m t
  | 0, t, h => h t (by omega)
  | 1, t, h => by
    show xor (c (t + 1)) (c t || rh R c t 1) = xor (c' (t + 1)) (c' t || rh R c' t 1)
    rw [h (t + 1) (by omega), h t (by omega), rh_congr R t (fun s hs => h s (by omega)) 1]
  | m + 2, t, h => by
    show xor (lc R c (m + 1) (t + 1)) (lc R c (m + 1) t || lc R c m t) =
      xor (lc R c' (m + 1) (t + 1)) (lc R c' (m + 1) t || lc R c' m t)
    rw [lc_congr R (m + 1) (t + 1) (fun s hs => h s (by omega)),
      lc_congr R (m + 1) t (fun s hs => h s (by omega)), lc_congr R m t (fun s hs => h s (by omega))]

/-- The single seed. -/
def seed (p : Int) : Bool := decide (p = 0)

theorem evol_seed : ∀ t p, evol seed t p = cell t p
  | 0, _ => rfl
  | t + 1, p => by
    show rule (evol seed t (p - 1)) (evol seed t p) (evol seed t (p + 1)) = cell (t + 1) p
    rw [evol_seed t (p - 1), evol_seed t p, evol_seed t (p + 1)]
    rfl

/-- **The left edge is essential, already for period 1.** For every `n` there is a
configuration that agrees with the single seed at all positions `≥ -n`, whose column `0`
agrees with the center column of rule 30 up to time `n`, and is white from then on. (It differs
from the seed at infinitely many positions `< -n`; by `no_column_eventually_constant`, no
left-finite such configuration exists for the seed itself.) -/
theorem seed_perturbation (n : Nat) :
    ∃ x : Int → Bool, (∀ p : Int, -(n : Int) ≤ p → x p = seed p) ∧
      (∀ t, t ≤ n → evol x t 0 = cell t 0) ∧ (∀ t, n < t → evol x t 0 = false) := by
  let c' : Nat → Bool := fun t => if t ≤ n then cell t 0 else false
  let cs : Nat → Bool := fun t => cell t 0
  have hreal := realize seed c'
  -- the seed itself is `conf seed cs`, by uniqueness
  have hseed : seed = conf seed cs := by
    refine unique (fun p hp => ((realize seed cs).1 p hp).symm) (fun t => ?_)
    rw [(realize seed cs).2 t, evol_seed]
  refine ⟨conf seed c', fun p hp => ?_, fun t ht => ?_, fun t ht => ?_⟩
  · by_cases h1 : 1 ≤ p
    · exact hreal.1 p h1
    · have e : conf seed c' p = lc seed c' (-p).toNat 0 := if_neg h1
      have e' : conf seed cs p = lc seed cs (-p).toNat 0 := if_neg h1
      rw [e, show seed p = conf seed cs p from congrFun hseed p, e']
      exact lc_congr seed (-p).toNat 0 (fun s hs => by
        show (if s ≤ n then cell s 0 else false) = cell s 0
        rw [if_pos (by omega)])
  · rw [hreal.2 t]; show (if t ≤ n then cell t 0 else false) = _; rw [if_pos ht]
  · rw [hreal.2 t]; show (if t ≤ n then cell t 0 else false) = _; rw [if_neg (by omega)]

end R30Realize
