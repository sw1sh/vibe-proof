import Ruliology.CellularAutomata.Rule30Jen

/-!
Independent check of claim "driven-left-jen" (all columns `-m`, `m ≥ 1`, not only `-1`).

`D x c t p`: the left half `p ≤ -1` evolves by rule 30, position `0` holds the driver `c t`,
positions `≥ 1` are `false` and are never read by positions `≤ -1`.
-/

namespace VerifyDrivenLeftJen
open Ruliology.CellularAutomata.Rule30Jen

def D (x : Int → Bool) (c : Nat → Bool) : Nat → Int → Bool
  | 0, p => if p < 0 then x p else if p = 0 then c 0 else false
  | t + 1, p => if p < 0 then rule (D x c t (p - 1)) (D x c t p) (D x c t (p + 1))
      else if p = 0 then c (t + 1) else false

section
variable (x : Int → Bool) (c : Nat → Bool)

theorem D_col0 : ∀ t, D x c t 0 = c t
  | 0 => by simp [D]
  | t + 1 => by simp [D]

theorem D_init {p : Int} (hp : p ≤ -1) : D x c 0 p = x p := by
  show (if p < 0 then x p else if p = 0 then c 0 else false) = x p
  rw [if_pos (by omega)]

theorem D_step (t : Nat) {p : Int} (hp : p ≤ -1) :
    D x c (t + 1) p = rule (D x c t (p - 1)) (D x c t p) (D x c t (p + 1)) := by
  show (if p < 0 then rule (D x c t (p - 1)) (D x c t p) (D x c t (p + 1))
      else if p = 0 then c (t + 1) else false) = _
  rw [if_pos (by omega)]

/-- The left edge, started at any time `t0` from a leftmost black cell `q ≤ -1`. -/
theorem edge {t0 : Nat} {q : Int} (hq : q ≤ -1) (hb : D x c t0 q = true)
    (hw : ∀ p, p < q → D x c t0 p = false) :
    ∀ s : Nat, (∀ p, p < q - s → D x c (t0 + s) p = false) ∧ D x c (t0 + s) (q - s) = true
  | 0 => by simpa using And.intro hw hb
  | s + 1 => by
    obtain ⟨ihw, ihb⟩ := edge hq hb hw s
    refine ⟨fun p hp => ?_, ?_⟩
    · rw [show t0 + (s + 1) = (t0 + s) + 1 by omega, D_step x c _ (by omega),
        ihw (p - 1) (by omega), ihw p (by omega), ihw (p + 1) (by omega)]
      rfl
    · rw [show t0 + (s + 1) = (t0 + s) + 1 by omega, D_step x c _ (by omega),
        ihw _ (by omega), ihw _ (by omega),
        show q - ((s + 1 : Nat) : Int) + 1 = q - (s : Int) by omega, ihb]
      rfl

/-- Left-permutivity inside the half-line. -/
theorem D_left (t : Nat) {i : Int} (hi : i ≤ -1) :
    D x c t (i - 1) = xor (D x c (t + 1) i) (D x c t i || D x c t (i + 1)) := by
  rw [D_step x c t hi]
  cases D x c t (i - 1) <;> cases D x c t i <;> cases D x c t (i + 1) <;> rfl

theorem periodic_left_all {T P : Nat} {i : Int} (hi : i + 1 ≤ 0)
    (h0 : ∀ t, T ≤ t → D x c (t + P) i = D x c t i)
    (h1 : ∀ t, T ≤ t → D x c (t + P) (i + 1) = D x c t (i + 1)) :
    ∀ m : Nat, (∀ t, T ≤ t → D x c (t + P) (i - m) = D x c t (i - m)) ∧
      ∀ t, T ≤ t → D x c (t + P) (i - m + 1) = D x c t (i - m + 1) := by
  intro m
  induction m with
  | zero => simpa using And.intro h0 h1
  | succ m ih =>
    refine ⟨fun t ht => ?_, ?_⟩
    · have hle : i - (m : Int) ≤ -1 := by omega
      rw [show i - ((m + 1 : Nat) : Int) = (i - (m : Int)) - 1 by omega,
        D_left x c (t + P) hle, D_left x c t hle, show t + P + 1 = (t + 1) + P by omega,
        ih.1 (t + 1) (by omega), ih.1 t ht, ih.2 t ht]
    · rw [show i - ((m + 1 : Nat) : Int) + 1 = i - (m : Int) by omega]
      exact ih.1

/-- Adjacent columns `i, i + 1 ≤ 0` are never both eventually periodic. -/
theorem not_adjacent {t0 : Nat} {q : Int} (hq : q ≤ -1) (hb : D x c t0 q = true)
    (hw : ∀ p, p < q → D x c t0 p = false) {i : Int} (hi : i + 1 ≤ 0)
    (h0 : EventuallyPeriodic fun t => D x c t i)
    (h1 : EventuallyPeriodic fun t => D x c t (i + 1)) : False := by
  obtain ⟨T, P, hP, hp0, hp1⟩ := common_period h0 h1
  obtain ⟨s, hs⟩ : ∃ s : Nat, s = P + T + (q - i).toNat := ⟨_, rfl⟩
  have hall := periodic_left_all x c hi hp0 hp1 (i - (q - (s : Int))).toNat
  have hper := hall.1 (t0 + s - P) (by omega)
  rw [show i - (((i - (q - (s : Int))).toNat : Nat) : Int) = q - (s : Int) by omega,
    show t0 + s - P + P = t0 + s by omega] at hper
  have hblack := (edge x c hq hb hw s).2
  have hwhite := (edge x c hq hb hw (s - P)).1 (q - (s : Int)) (by omega)
  rw [show t0 + (s - P) = t0 + s - P by omega] at hwhite
  rw [hblack, hwhite] at hper
  exact absurd hper (by decide)

/-! ### The strip between columns `j < k ≤ 0` -/

def strip (j k : Int) (t : Nat) : List Bool :=
  (List.range (k - j - 1).toNat).map fun (r : Nat) => D x c t (j + 1 + (r : Int))

set_option linter.unusedSimpArgs false in
theorem strip_agree {j k : Int} (hjk : j < k) (hk : k ≤ 0) {t₁ t₂ : Nat}
    (hs : strip x c j k t₁ = strip x c j k t₂)
    (hb : ∀ r, D x c (t₁ + r) j = D x c (t₂ + r) j ∧ D x c (t₁ + r) k = D x c (t₂ + r) k) :
    ∀ r, ∀ i, j ≤ i → i ≤ k → D x c (t₁ + r) i = D x c (t₂ + r) i := by
  intro r
  induction r with
  | zero =>
    intro i hi1 hi2
    by_cases e1 : i = j
    · subst e1; exact (hb 0).1
    by_cases e2 : i = k
    · subst e2; exact (hb 0).2
    have := congrArg (fun l => l.getD (i - j - 1).toNat false) hs
    simp only [strip, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_range (show (i - j - 1).toNat < (k - j - 1).toNat by omega),
      Option.map_some, Option.getD_some] at this
    rwa [show j + 1 + (((i - j - 1).toNat : Nat) : Int) = i by omega] at this
  | succ r ih =>
    intro i hi1 hi2
    by_cases e1 : i = j
    · subst e1; exact (hb (r + 1)).1
    by_cases e2 : i = k
    · subst e2; exact (hb (r + 1)).2
    rw [show t₁ + (r + 1) = (t₁ + r) + 1 by omega, show t₂ + (r + 1) = (t₂ + r) + 1 by omega,
      D_step x c _ (by omega), D_step x c _ (by omega),
      ih (i - 1) (by omega) (by omega), ih i (by omega) (by omega),
      ih (i + 1) (by omega) (by omega)]

theorem between_periodic {j k : Int} (hjk : j + 1 < k) (hk : k ≤ 0)
    (hj : EventuallyPeriodic fun t => D x c t j) (hk' : EventuallyPeriodic fun t => D x c t k) :
    EventuallyPeriodic fun t => D x c t (j + 1) := by
  obtain ⟨T, P, hP, hpj, hpk⟩ := common_period hj hk'
  obtain ⟨m, n, hmn, -, he⟩ := pigeonhole (k - j - 1).toNat (fun m => strip x c j k (T + m * P))
    (fun m => by simp only [strip, List.length_map, List.length_range])
  have hmP : m * P ≤ n * P := Nat.mul_le_mul_right _ (by omega)
  refine ⟨T + m * P, (n - m) * P, Nat.mul_pos (by omega) hP, fun t ht => ?_⟩
  have key := strip_agree x c (by omega) hk he (fun r => ⟨?_, ?_⟩) (t - (T + m * P)) (j + 1)
    (by omega) (by omega)
  · rw [show T + m * P + (t - (T + m * P)) = t by omega,
      show T + n * P + (t - (T + m * P)) = t + (n - m) * P by rw [Nat.sub_mul]; omega] at key
    exact key.symm
  · rw [show T + n * P + r = (T + m * P + r) + (n - m) * P by rw [Nat.sub_mul]; omega]
    exact (periodic_mul (f := fun t => D x c t j) hpj (n - m) _ (by omega)).symm
  · rw [show T + n * P + r = (T + m * P + r) + (n - m) * P by rw [Nat.sub_mul]; omega]
    exact (periodic_mul (f := fun t => D x c t k) hpk (n - m) _ (by omega)).symm

/-- **Main theorem (any start time `t0`).** If at time `t0` the left half has a leftmost black
cell, and the driver is eventually periodic, then no column `-m`, `m ≥ 1`, is eventually
periodic. -/
theorem main {t0 : Nat} {q : Int} (hq : q ≤ -1) (hb : D x c t0 q = true)
    (hw : ∀ p, p < q → D x c t0 p = false) (hc : EventuallyPeriodic c) :
    ∀ m : Nat, 1 ≤ m → ¬ EventuallyPeriodic fun t => D x c t (-(m : Int)) := by
  intro m hm hpm
  have hc' : EventuallyPeriodic fun t => D x c t 0 := by
    have : (fun t => D x c t 0) = c := funext (D_col0 x c)
    rw [this]; exact hc
  by_cases h1 : m = 1
  · subst h1
    exact not_adjacent x c hq hb hw (i := -1) (by omega) hpm (by simpa using hc')
  · have hnext := between_periodic x c (j := -(m : Int)) (k := 0) (by omega) (Int.le_refl 0) hpm hc'
    exact not_adjacent x c hq hb hw (i := -(m : Int)) (by omega) hpm hnext

end

/-- A left-finite, not all white initial left half has a leftmost black cell. -/
theorem leftmost (x : Int → Bool) (N : Int) (hN : ∀ p, p < N → x p = false) :
    ∀ n : Nat, (∃ p, p ≤ N + n ∧ x p = true) → ∃ q, q ≤ N + n ∧ x q = true ∧ ∀ r, r < q → x r = false
  | 0, ⟨p, hp, hx⟩ => by
    have : ¬ p < N := fun h => by rw [hN p h] at hx; exact absurd hx (by decide)
    exact ⟨p, hp, hx, fun r hr => hN r (by omega)⟩
  | n + 1, ⟨p, hp, hx⟩ => by
    by_cases h : ∃ p', p' ≤ N + n ∧ x p' = true
    · obtain ⟨q, hq, hxq, hw⟩ := leftmost x N hN n h
      exact ⟨q, by omega, hxq, hw⟩
    · refine ⟨p, hp, hx, fun r hr => ?_⟩
      cases e : x r with
      | false => rfl
      | true =>
        exact absurd ⟨r, by
          by_cases hrn : r ≤ N + n
          · exact hrn
          · exfalso; apply h; exact ⟨p, by
              by_cases hpn : p ≤ N + n
              · exact hpn
              · omega, hx⟩, e⟩ h

/-- **The claim as stated**: initial left half left-finite and not all white, driver eventually
periodic ⟹ no column `-m` (`m ≥ 1`) is eventually periodic. -/
theorem claim (x : Int → Bool) (c : Nat → Bool)
    (hfin : ∃ N : Int, ∀ p, p < N → x p = false)
    (hne : ∃ p, p ≤ -1 ∧ x p = true)
    (hc : EventuallyPeriodic c) :
    ∀ m : Nat, 1 ≤ m → ¬ EventuallyPeriodic fun t => D x c t (-(m : Int)) := by
  obtain ⟨N, hN⟩ := hfin
  obtain ⟨p, hp, hxp⟩ := hne
  have hpN : N ≤ p := by
    by_cases h : p < N
    · rw [hN p h] at hxp; exact absurd hxp (by decide)
    · omega
  obtain ⟨q, hqle, hxq, hwq⟩ := leftmost x N hN (p - N).toNat ⟨p, by omega, hxp⟩
  -- q ≤ -1: otherwise p < q (p ≤ -1) with x p = true
  have hq : q ≤ -1 := by
    by_cases h : q ≤ -1
    · exact h
    · have := hwq p (by omega); rw [this] at hxp; exact absurd hxp (by decide)
  exact main x c (t0 := 0) hq (by rw [D_init x c hq]; exact hxq)
    (fun r hr => by rw [D_init x c (by omega)]; exact hwq r hr) hc

/-- **Seed corollary**: all-white left half, driver with `c 0 = true` (e.g. `1 · w^∞`),
eventually periodic ⟹ no column `-m` is eventually periodic. -/
theorem seed (c : Nat → Bool) (h0 : c 0 = true) (hc : EventuallyPeriodic c) :
    ∀ m : Nat, 1 ≤ m → ¬ EventuallyPeriodic fun t => D (fun _ => false) c t (-(m : Int)) := by
  have hb : D (fun _ => false) c 1 (-1) = true := by
    rw [D_step _ _ 0 (by omega), D_init _ _ (by omega), D_init _ _ (by omega),
      show (-1 : Int) + 1 = 0 by rfl, D_col0, h0]
    rfl
  have hw : ∀ p, p < -1 → D (fun _ => false) c 1 p = false := by
    intro p hp
    rw [D_step _ _ 0 (by omega), D_init _ _ (by omega), D_init _ _ (by omega),
      D_init _ _ (by omega)]
    rfl
  exact main _ c (t0 := 1) (q := -1) (by omega) hb hw hc

/-- `1 · w^∞` is eventually periodic, for any word given as `w : Nat → Bool` of length `L ≥ 1`. -/
theorem seedWord_periodic (w : Nat → Bool) (L : Nat) (hL : 0 < L) :
    EventuallyPeriodic fun t => if t = 0 then true else w ((t - 1) % L) := by
  refine ⟨1, L, hL, fun t ht => ?_⟩
  simp only [show t + L ≠ 0 by omega, show t ≠ 0 by omega, if_false]
  rw [show t + L - 1 = (t - 1) + L by omega, Nat.add_mod_right]

theorem seed_word (w : Nat → Bool) (L : Nat) (hL : 0 < L) :
    ∀ m : Nat, 1 ≤ m → ¬ EventuallyPeriodic fun t =>
      D (fun _ => false) (fun t => if t = 0 then true else w ((t - 1) % L)) t (-(m : Int)) :=
  seed _ (by simp) (seedWord_periodic w L hL)

end VerifyDrivenLeftJen

#print axioms VerifyDrivenLeftJen.claim
#print axioms VerifyDrivenLeftJen.seed_word
