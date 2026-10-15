import Ruliology.CellularAutomata.Rule30Diagonals

/-!
# Independent check of the claim `mono_step_doubling` (right-diagonal periods of rule 30)

Written from scratch against `Rule30Jen.cell` / `Rule30Diagonals.R`; it does not import the
`diagonal` agent's draft.

* (a) `mono_all`: if `R (j+1)` has period `H` then every `R i`, `i ≤ j`, has period `H`
  (for every `j` and every `H`; the claim's restriction "H = 1 or H even" is not needed).
  `e_mono`: `e_j ≤ e_{j+1}`.
* (b) `shift_formula`: if `R j` has period `H` then `R (j+1) (t+H) = R (j+1) t xor R (j+1) H`.
* (c) `e_step`: `e_{j+1} = e_j + [R_{j+1}(2^{e_j})]`; `antiperiod`, `half_black`.
* (d) `halve_inp`: the halving lemma with the hypothesis on the input `g_{j+1}` only;
  `inp_period`, `inp_least_period`: for `j ≥ 3` the least period of `g_j` is `2^{e_{j-1}}`;
  `S_rule`: `e_j - e_{j-1}` is the parity of `g_j` over `[0, 2^{e_{j-1}})`.
-/

namespace Ruliology.CellularAutomata
namespace VerifyMonoStep

open Rule30Jen Rule30Diagonals

/-! ### Basic facts F1, F2, F3 -/

/-- F1: outside the light cone. -/
theorem R_lt {j t : Nat} (h : 2 * t < j) : R j t = false :=
  cell_eq_false_of_lt t _ (by omega)

/-- F2: `R_j(ceil(j/2)) = 1` for `j ≥ 1`. -/
theorem R_half {j : Nat} (h : 1 ≤ j) : R j ((j + 1) / 2) = true := by
  obtain ⟨s, hs⟩ : ∃ s, j = 2 * s ∨ j = 2 * s + 1 := ⟨j / 2, by omega⟩
  rcases hs with rfl | rfl
  · rw [show (2 * s + 1) / 2 = s by omega]
    show cell s ((s : Int) - ((2 * s : Nat) : Int)) = true
    rw [cell_congr (show (s : Int) - ((2 * s : Nat) : Int) = -(s : Int) by omega)]
    exact cell_left_edge s
  · rw [show (2 * s + 1 + 1) / 2 = s + 1 by omega]
    show cell (s + 1) (((s + 1 : Nat) : Int) - ((2 * s + 1 : Nat) : Int)) = true
    rw [cell_congr (show ((s + 1 : Nat) : Int) - ((2 * s + 1 : Nat) : Int)
      = ((1 : Nat) : Int) - ((s + 1 : Nat) : Int) by omega)]
    exact D_one s

theorem mod2_add (a b : Nat) : ((a + b) % 2 == 1) = xor (a % 2 == 1) (b % 2 == 1) := by
  rcases Nat.mod_two_eq_zero_or_one a with ha | ha <;>
  rcases Nat.mod_two_eq_zero_or_one b with hb | hb
  · have h : (a + b) % 2 = 0 := by omega
    simp [h, ha, hb]
  · have h : (a + b) % 2 = 1 := by omega
    simp [h, ha, hb]
  · have h : (a + b) % 2 = 1 := by omega
    simp [h, ha, hb]
  · have h : (a + b) % 2 = 0 := by omega
    simp [h, ha, hb]

/-- `R_1 = t mod 2`. -/
theorem R_one_eq : ∀ t, R 1 t = (t % 2 == 1)
  | 0 => R_lt (by omega)
  | t + 1 => by
    rw [R_one_succ, R_one_eq t, mod2_add]
    cases (t % 2 == 1) <;> rfl

/-- F3: `R_2 = R_1`. -/
theorem R_two_eq_one : ∀ t, R 2 t = R 1 t
  | 0 => by rw [R_lt (show 2 * 0 < 2 by omega), R_lt (show 2 * 0 < 1 by omega)]
  | t + 1 => by
    have s := R_step 0 t
    have s' : R 2 (t + 1) = xor (R 2 t) (R 1 t || R 0 t) := s
    rw [s', R_one_succ, R_zero, R_two_eq_one t]
    cases R 1 t <;> rfl

/-! ### Periods -/

/-- `f` repeats with period `p` from time `0`. -/
def PerF (f : Nat → Bool) (p : Nat) : Prop := ∀ t, f (t + p) = f t

/-- `R j` repeats with period `p` from time `0`. -/
abbrev Per (j p : Nat) : Prop := PerF (R j) p

theorem PerF.mul {f : Nat → Bool} {p : Nat} (h : PerF f p) : ∀ n, PerF f (n * p)
  | 0 => fun t => by rw [Nat.zero_mul, Nat.add_zero]
  | n + 1 => fun t => by
    rw [Nat.add_mul, Nat.one_mul, ← Nat.add_assoc, h, PerF.mul h n t]

theorem PerF.pow_mono {f : Nat → Bool} {a b : Nat} (h : PerF f (2 ^ a)) (hab : a ≤ b) :
    PerF f (2 ^ b) := by
  have := h.mul (2 ^ (b - a))
  rwa [← Nat.pow_add, show b - a + a = b by omega] at this

theorem PerF.mod {f : Nat → Bool} {p q : Nat} (hp : PerF f p) (hq : PerF f q) :
    PerF f (q % p) := by
  intro t
  have hd : q % p + q / p * p = q := by rw [Nat.mul_comm]; exact Nat.mod_add_div q p
  have e := hp.mul (q / p) (t + q % p)
  rw [Nat.add_assoc, hd, hq] at e
  exact e.symm

/-- Periods `p` and `q` give the period `gcd p q`. -/
theorem PerF.gcd {f : Nat → Bool} (p q : Nat) : PerF f p → PerF f q → PerF f (Nat.gcd p q) := by
  refine Nat.gcd.induction (P := fun p q => PerF f p → PerF f q → PerF f (Nat.gcd p q)) p q ?_ ?_
  · intro n _ hn
    rw [Nat.gcd_zero_left]; exact hn
  · intro m n _ ih hm hn
    rw [Nat.gcd_rec]
    exact ih (hm.mod hn) hm

theorem per_zero (p : Nat) : Per 0 p := fun t => by rw [R_zero, R_zero]

/-- A diagonal `j ≥ 1` is not constant. -/
theorem not_per_one {j : Nat} (hj : 1 ≤ j) : ¬ Per j 1 := by
  intro h
  have hc : ∀ t, R j t = false := by
    intro t
    induction t with
    | zero => exact R_lt (by omega)
    | succ t ih => rw [h t, ih]
  have := R_half hj
  rw [hc] at this
  exact absurd this (by decide)

/-- (L): accumulating an `L`-periodic input shifts by a constant over `L` steps. -/
theorem accum_shift {x g : Nat → Bool} {L : Nat} (hx : ∀ t, x (t + 1) = xor (x t) (g t))
    (hg : ∀ t, g (t + L) = g t) : ∀ t, x (t + L) = xor (x t) (xor (x L) (x 0)) := by
  have hconst : ∀ t, xor (x (t + L)) (x t) = xor (x L) (x 0) := by
    intro t
    induction t with
    | zero => rw [Nat.zero_add]
    | succ t ih =>
      rw [show t + 1 + L = (t + L) + 1 by omega, hx (t + L), hx t, hg t, ← ih]
      cases x (t + L) <;> cases x t <;> cases g t <;> rfl
  intro t
  have h := hconst t
  revert h
  cases x (t + L) <;> cases x t <;> cases xor (x L) (x 0) <;> simp

/-! ### The halving lemma -/

/-- Diagonals `a` and `a + 1` are white at times `H + t`, `t < M`. -/
def Z (H a M : Nat) : Prop := ∀ t, t < M → R a (H + t) = false ∧ R (a + 1) (H + t) = false

/-- Step 2 (descent). -/
theorem Z_down {H a M : Nat} (h : Z H (a + 2) (M + 1)) : Z H a M := by
  intro t ht
  obtain ⟨h2, h3⟩ := h t (by omega)
  obtain ⟨h2', h3'⟩ := h (t + 1) (by omega)
  -- recurrence of diagonal a + 3 and of diagonal a + 2 at time H + t
  have s3 : R (a + 1 + 2) (H + t + 1) = xor (R (a + 1 + 2) (H + t))
      (R (a + 1 + 1) (H + t) || R (a + 1) (H + t)) := R_step (a + 1) (H + t)
  have s2 : R (a + 2) (H + t + 1) = xor (R (a + 2) (H + t))
      (R (a + 1) (H + t) || R a (H + t)) := R_step a (H + t)
  rw [show a + 1 + 2 = a + 2 + 1 by omega, show a + 1 + 1 = a + 2 by omega,
    show H + t + 1 = H + (t + 1) by omega, h3', h3, h2] at s3
  rw [show H + t + 1 = H + (t + 1) by omega, h2', h2] at s2
  constructor
  · revert s2 s3; cases R (a + 1) (H + t) <;> cases R a (H + t) <;> simp
  · revert s3; cases R (a + 1) (H + t) <;> simp

theorem Z_iter {H a M : Nat} : ∀ s, Z H (a + 2 * s) (M + s) → Z H a M
  | 0, h => by simpa using h
  | s + 1, h => by
    have h' : Z H ((a + 2) + 2 * s) ((M + 1) + s) := by
      rw [show (a + 2) + 2 * s = a + 2 * (s + 1) by omega,
        show (M + 1) + s = M + (s + 1) by omega]
      exact h
    exact Z_down (Z_iter s h')

theorem Z_mono {H a M M' : Nat} (h : Z H a M) (hM : M' ≤ M) : Z H a M' :=
  fun t ht => h t (by omega)

/-- Descending from `Z H (n+1) ((n+2)/2)`: every diagonal `2 ≤ i ≤ n + 2` is white at time `H`. -/
theorem Z_bottom {H n : Nat} (hZ : Z H (n + 1) ((n + 2) / 2)) :
    ∀ i, 2 ≤ i → i ≤ n + 2 → R i H = false := by
  intro i hi1 hi2
  rcases Nat.mod_two_eq_zero_or_one (n + 2 - i) with hp | hp
  · have hz : Z H ((i - 1) + 2 * ((n + 2 - i) / 2)) (1 + (n + 2 - i) / 2) := by
      rw [show (i - 1) + 2 * ((n + 2 - i) / 2) = n + 1 by omega]
      exact Z_mono hZ (by omega)
    have := (Z_iter _ hz) 0 (by omega)
    rw [Nat.add_zero, show i - 1 + 1 = i by omega] at this
    exact this.2
  · have hz : Z H (i + 2 * ((n + 1 - i) / 2)) (1 + (n + 1 - i) / 2) := by
      rw [show i + 2 * ((n + 1 - i) / 2) = n + 1 by omega]
      exact Z_mono hZ (by omega)
    have := (Z_iter _ hz) 0 (by omega)
    rw [Nat.add_zero] at this
    exact this.1

/-- Step 3: from the white strip, every diagonal `i ≤ n + 2` has period `H`. -/
theorem halve_of_Z {H n : Nat} (hZ : Z H (n + 1) ((n + 2) / 2)) :
    ∀ i, i ≤ n + 2 → Per i H := by
  have hb := Z_bottom hZ
  have hH : H % 2 = 0 := by
    have h2 := hb 2 (by omega) (by omega)
    rw [R_two_eq_one, R_one_eq] at h2
    rcases Nat.mod_two_eq_zero_or_one H with h | h
    · exact h
    · rw [h] at h2; exact absurd h2 (by decide)
  have pair : ∀ m, (m ≤ n + 2 → Per m H) ∧ (m + 1 ≤ n + 2 → Per (m + 1) H) := by
    intro m
    induction m with
    | zero =>
      refine ⟨fun _ => per_zero H, fun _ => ?_⟩
      intro t
      show R 1 (t + H) = R 1 t
      rw [R_one_eq, R_one_eq, show (t + H) % 2 = t % 2 by omega]
    | succ m ih =>
      refine ⟨ih.2, fun hm => ?_⟩
      have pa : Per m H := ih.1 (by omega)
      have pb : Per (m + 1) H := ih.2 (by omega)
      have sh := accum_shift (x := R (m + 2)) (g := fun t => R (m + 1) t || R m t) (L := H)
        (fun t => R_step m t)
        (fun t => by
          show (R (m + 1) (t + H) || R m (t + H)) = (R (m + 1) t || R m t)
          rw [pa t, pb t])
      intro t
      show R (m + 2) (t + H) = R (m + 2) t
      rw [sh t, R_lt (show 2 * 0 < m + 2 by omega), hb (m + 2) (by omega) (by omega)]
      cases R (m + 2) t <;> rfl
  exact fun i hi => (pair i).1 hi

/-- Step 1: a period `H` of diagonal `n + 3` yields the white strip. -/
theorem Z_of_per {H n : Nat} (h : Per (n + 3) H) : Z H (n + 1) ((n + 2) / 2) := by
  intro t ht
  have s : R (n + 3) (H + t + 1) = xor (R (n + 3) (H + t))
      (R (n + 2) (H + t) || R (n + 1) (H + t)) := R_step (n + 1) (H + t)
  have e1 : R (n + 3) (H + t + 1) = false := by
    rw [show H + t + 1 = (t + 1) + H by omega, h]
    exact R_lt (by omega)
  have e2 : R (n + 3) (H + t) = false := by
    rw [show H + t = t + H by omega, h]
    exact R_lt (by omega)
  rw [e1, e2] at s
  show R (n + 1) (H + t) = false ∧ R (n + 2) (H + t) = false
  revert s; cases R (n + 1) (H + t) <;> cases R (n + 2) (H + t) <;> simp

/-- (a) for `j = n + 2 ≥ 2`, any `H`. -/
theorem halve {H n : Nat} (h : Per (n + 3) H) : ∀ i, i ≤ n + 2 → Per i H :=
  halve_of_Z (Z_of_per h)

/-- (a) for every `j` and every `H`. -/
theorem mono_all {j H : Nat} (h : Per (j + 1) H) : ∀ i, i ≤ j → Per i H := by
  rcases j with _ | _ | n
  · intro i hi
    rw [show i = 0 by omega]; exact per_zero H
  · intro i hi
    rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl
    · exact per_zero H
    · intro t
      have := h t
      rw [R_two_eq_one, R_two_eq_one] at this
      exact this
  · exact halve h

/-! ### (b) shift formula -/

theorem shift_formula {j H : Nat} (h : Per j H) :
    ∀ t, R (j + 1) (t + H) = xor (R (j + 1) t) (R (j + 1) H) := by
  rcases j with _ | j
  · intro t
    show R 1 (t + H) = xor (R 1 t) (R 1 H)
    rw [R_one_eq, R_one_eq, R_one_eq, mod2_add]
  · have hj : Per j H := mono_all h j (Nat.le_refl j)
    have sh := accum_shift (x := R (j + 2)) (g := fun t => R (j + 1) t || R j t) (L := H)
      (fun t => R_step j t)
      (fun t => by
        show (R (j + 1) (t + H) || R j (t + H)) = (R (j + 1) t || R j t)
        rw [h t, hj t])
    rw [R_lt (show 2 * 0 < j + 2 by omega)] at sh
    intro t
    show R (j + 2) (t + H) = xor (R (j + 2) t) (R (j + 2) H)
    rw [sh t]; cases R (j + 2) H <;> cases R (j + 2) t <;> rfl

/-! ### (c) the exponent `e_j` -/

/-- `e` is the least exponent with `R j` of period `2^e`. -/
def IsE (j e : Nat) : Prop := Per j (2 ^ e) ∧ ∀ k, k < e → ¬ Per j (2 ^ k)

theorem IsE.le {j e k : Nat} (he : IsE j e) (hk : Per j (2 ^ k)) : e ≤ k :=
  Nat.le_of_not_lt (fun hlt => he.2 k hlt hk)

theorem IsE.unique {j e e' : Nat} (he : IsE j e) (he' : IsE j e') : e = e' :=
  Nat.le_antisymm (he.le he'.1) (he'.le he.1)

theorem exists_IsE (j : Nat) : ∃ e, IsE j e := by
  have key : ∀ n, Per j (2 ^ n) → ∃ e, IsE j e := by
    intro n
    induction n with
    | zero => intro h; exact ⟨0, h, fun k hk => absurd hk (Nat.not_lt_zero k)⟩
    | succ n ih =>
      intro h
      by_cases hn : Per j (2 ^ n)
      · exact ih hn
      · exact ⟨n + 1, h, fun k hk hpk => hn (PerF.pow_mono hpk (by omega))⟩
  exact key j (R_periodic j)

/-- Monotonicity `e_j ≤ e_{j+1}`. -/
theorem e_mono {j e e' : Nat} (he : IsE j e) (he' : IsE (j + 1) e') : e ≤ e' :=
  he.le (mono_all he'.1 j (Nat.le_refl j))

/-- (c) `e_{j+1} = e_j + [R_{j+1}(2^{e_j})]`. -/
theorem e_step {j e e' : Nat} (he : IsE j e) (he' : IsE (j + 1) e') :
    e' = e + (if R (j + 1) (2 ^ e) then 1 else 0) := by
  have hmono : e ≤ e' := e_mono he he'
  have sf := shift_formula he.1
  cases hb : R (j + 1) (2 ^ e)
  · have hp : Per (j + 1) (2 ^ e) := fun t => by
      rw [sf t, hb]; cases R (j + 1) t <;> rfl
    have := he'.le hp
    simp; omega
  · have hnp : ¬ Per (j + 1) (2 ^ e) := fun hp => by
      have h0 := hp 0
      rw [Nat.zero_add, hb, R_lt (show 2 * 0 < j + 1 by omega)] at h0
      exact absurd h0 (by decide)
    have hp2 : Per (j + 1) (2 ^ (e + 1)) := fun t => by
      rw [Nat.pow_succ, show 2 ^ e * 2 = 2 ^ e + 2 ^ e by omega, ← Nat.add_assoc, sf, sf, hb]
      cases R (j + 1) t <;> rfl
    have h1 := he'.le hp2
    have h2 : e' ≠ e := fun heq => hnp (heq ▸ he'.1)
    simp; omega

/-- When the period doubles, a shift by half the new period complements the diagonal. -/
theorem antiperiod {j e : Nat} (h : Per j (2 ^ e)) (hb : R (j + 1) (2 ^ e) = true) :
    ∀ t, R (j + 1) (t + 2 ^ e) = !R (j + 1) t := by
  intro t; rw [shift_formula h t, hb]; cases R (j + 1) t <;> rfl

/-- Number of `s ∈ [a, a + n)` with `f s`. -/
def cnt (f : Nat → Bool) (a : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => cnt f a n + (if f (a + n) then 1 else 0)

theorem cnt_add (f : Nat → Bool) (a n : Nat) :
    ∀ m, cnt f a (n + m) = cnt f a n + cnt f (a + n) m
  | 0 => rfl
  | m + 1 => by
    show cnt f a (n + m) + (if f (a + (n + m)) then 1 else 0)
      = cnt f a n + (cnt f (a + n) m + (if f (a + n + m) then 1 else 0))
    rw [cnt_add f a n m, show a + (n + m) = a + n + m by omega, Nat.add_assoc]

theorem cnt_compl {f : Nat → Bool} {L : Nat} (h : ∀ s, f (s + L) = !f s) (a : Nat) :
    ∀ n, cnt f (a + L) n + cnt f a n = n
  | 0 => rfl
  | n + 1 => by
    show (cnt f (a + L) n + (if f (a + L + n) then 1 else 0))
      + (cnt f a n + (if f (a + n) then 1 else 0)) = n + 1
    have ih := cnt_compl h a n
    rw [show a + L + n = (a + n) + L by omega, h (a + n)]
    cases f (a + n) <;> simp <;> omega

/-- When the period doubles, every window of one full period is exactly half black. -/
theorem half_black {j e : Nat} (h : Per j (2 ^ e)) (hb : R (j + 1) (2 ^ e) = true) (a : Nat) :
    cnt (R (j + 1)) a (2 ^ (e + 1)) = 2 ^ e := by
  rw [Nat.pow_succ, show 2 ^ e * 2 = 2 ^ e + 2 ^ e by omega, cnt_add]
  have := cnt_compl (antiperiod h hb) a (2 ^ e)
  omega

/-! ### (d) the input `g` -/

/-- `inp j` is the input of diagonal `j + 2`: `R (j+2) (t+1) = R (j+2) t xor inp j t`.
In the claim's notation `g_{j+2} = inp j`. -/
def inp (j t : Nat) : Bool := R (j + 1) t || R j t

theorem inp_step (j t : Nat) : R (j + 2) (t + 1) = xor (R (j + 2) t) (inp j t) := R_step j t

/-- Step 1 under the weaker hypothesis that only the input `g_{n+3} = inp (n+1)` has period `H`. -/
theorem Z_of_inp_per {H n : Nat} (h : PerF (inp (n + 1)) H) : Z H (n + 1) ((n + 2) / 2) := by
  intro t ht
  have e : (R (n + 2) (H + t) || R (n + 1) (H + t)) = false := by
    show inp (n + 1) (H + t) = false
    rw [show H + t = t + H by omega, h t]
    show (R (n + 2) t || R (n + 1) t) = false
    rw [R_lt (show 2 * t < n + 2 by omega), R_lt (show 2 * t < n + 1 by omega)]
    rfl
  show R (n + 1) (H + t) = false ∧ R (n + 2) (H + t) = false
  revert e; cases R (n + 1) (H + t) <;> cases R (n + 2) (H + t) <;> simp

/-- (a') The halving lemma with the hypothesis on the input only (any `H`). -/
theorem halve_inp {H n : Nat} (h : PerF (inp (n + 1)) H) : ∀ i, i ≤ n + 2 → Per i H :=
  halve_of_Z (Z_of_inp_per h)

theorem odd_dvd_two_pow : ∀ k c, c % 2 = 1 → c ∣ 2 ^ k → c = 1
  | 0, _, _, h => Nat.eq_one_of_dvd_one h
  | k + 1, c, hc, ⟨q, hq⟩ => by
    have hq2 : q % 2 = 0 := by
      rcases Nat.mod_two_eq_zero_or_one q with h | h
      · exact h
      · exfalso
        have h1 : (c * q) % 2 = 1 := by rw [Nat.mul_mod, hc, h]
        have h2 : 2 ^ (k + 1) % 2 = 0 := by rw [Nat.pow_succ, Nat.mul_mod_left]
        rw [hq] at h2; omega
    obtain ⟨q', rfl⟩ : ∃ q', q = 2 * q' := ⟨q / 2, by omega⟩
    apply odd_dvd_two_pow k c hc
    refine ⟨q', ?_⟩
    rw [Nat.pow_succ, Nat.mul_left_comm] at hq
    omega

theorem dvd_two_pow_succ {d k : Nat} (h : d ∣ 2 ^ (k + 1)) : d = 2 ^ (k + 1) ∨ d ∣ 2 ^ k := by
  obtain ⟨c, hc⟩ := h
  rcases Nat.mod_two_eq_zero_or_one c with h0 | h1
  · right
    obtain ⟨c', rfl⟩ : ∃ c', c = 2 * c' := ⟨c / 2, by omega⟩
    refine ⟨c', ?_⟩
    rw [Nat.pow_succ, Nat.mul_left_comm] at hc
    omega
  · left
    have : c = 1 := odd_dvd_two_pow (k + 1) c h1 ⟨d, by rw [hc, Nat.mul_comm]⟩
    rw [hc, this, Nat.mul_one]

/-- The input of diagonal `n + 3` has period `2^{e_{n+2}}`. -/
theorem inp_period {n e : Nat} (he : IsE (n + 2) e) : PerF (inp (n + 1)) (2 ^ e) := by
  have h2 : Per (n + 2) (2 ^ e) := he.1
  have h1 : Per (n + 1) (2 ^ e) := mono_all (j := n + 1) h2 (n + 1) (Nat.le_refl _)
  intro t
  show (R (n + 2) (t + 2 ^ e) || R (n + 1) (t + 2 ^ e)) = (R (n + 2) t || R (n + 1) t)
  rw [h2 t, h1 t]

/-- (d) Every period `p > 0` of the input `g_{n+3}` is a multiple of `2^{e_{n+2}}`; with
`inp_period`, the least period of `g_j` is exactly `2^{e_{j-1}}` for `j = n + 3 ≥ 3`. -/
theorem inp_least_period {n e : Nat} (he : IsE (n + 2) e) {p : Nat}
    (hp : PerF (inp (n + 1)) p) : 2 ^ e ∣ p := by
  have hd := PerF.gcd p (2 ^ e) hp (inp_period he)
  have hdvd : Nat.gcd p (2 ^ e) ∣ 2 ^ e := Nat.gcd_dvd_right p (2 ^ e)
  rcases e with _ | e
  · exact Nat.one_dvd p
  · rcases dvd_two_pow_succ hdvd with heq | hdv
    · rw [← heq]; exact Nat.gcd_dvd_left p (2 ^ (e + 1))
    · exfalso
      obtain ⟨c, hc⟩ := hdv
      have hpe : PerF (inp (n + 1)) (2 ^ e) := by
        rw [hc, Nat.mul_comm]; exact hd.mul c
      have := halve_inp (n := n) hpe (n + 2) (Nat.le_refl _)
      exact he.2 e (Nat.lt_succ_self e) this

/-- The least period, as an inequality: no smaller positive period. -/
theorem inp_no_smaller_period {n e : Nat} (he : IsE (n + 2) e) {p : Nat} (hp0 : 0 < p)
    (hp : PerF (inp (n + 1)) p) : 2 ^ e ≤ p :=
  Nat.le_of_dvd hp0 (inp_least_period he hp)

/-- (d) S-rule: for `j = n + 3`, `e_j = e_{j-1} + parity(g_j on [0, 2^{e_{j-1}}))`, where
`2^{e_{j-1}}` is the least period of `g_j` (`inp_period`, `inp_least_period`). -/
theorem S_rule {n e e' : Nat} (he : IsE (n + 2) e) (he' : IsE (n + 3) e') :
    e' = e + (if (((List.range (2 ^ e)).filter (inp (n + 1))).length % 2 == 1) then 1 else 0) := by
  have h := e_step he he'
  have hp : R (n + 3) (2 ^ e)
      = (((List.range (2 ^ e)).filter (inp (n + 1))).length % 2 == 1) := R_eq_parity (n + 1) (2 ^ e)
  have h' : e' = e + (if R (n + 3) (2 ^ e) then 1 else 0) := h
  rw [hp] at h'
  exact h'

end VerifyMonoStep
end Ruliology.CellularAutomata

open Ruliology.CellularAutomata.VerifyMonoStep in
#print axioms mono_all
open Ruliology.CellularAutomata.VerifyMonoStep in
#print axioms shift_formula
open Ruliology.CellularAutomata.VerifyMonoStep in
#print axioms e_step
open Ruliology.CellularAutomata.VerifyMonoStep in
#print axioms half_black
open Ruliology.CellularAutomata.VerifyMonoStep in
#print axioms inp_least_period
open Ruliology.CellularAutomata.VerifyMonoStep in
#print axioms inp_no_smaller_period
open Ruliology.CellularAutomata.VerifyMonoStep in
#print axioms S_rule
open Ruliology.CellularAutomata.VerifyMonoStep in
#print axioms exists_IsE
