/-!
# P312 never looks back past `f[-3]`

Catalog entry `p312-lookback-bound`.

Wolfram's P312 comes from *Nestedly Recursive Functions* (2024), section "A Closer Look at P312":
<https://writings.stephenwolfram.com/2024/09/nestedly-recursive-functions/#a-closer-look-at-p312--fn--3--fn---fn---2>

    f[n_ /; n <= 0] = 1;  f[n_] := 3 + f[n - f[n - 2]]

The essay notes that "the only values needed are f[–3], f[–2], f[–1] and f[0]". Wolfram's 2024
working notes list "Get a proof that this only gets to f[-3]" as a to-do. We prove it.

* `lookback_ge_neg_three`: for every `n ≥ 1` the lookback index `n - f[n-2]` is at least `-3`.
  Equality holds at `n = 4` (`lookback_four`).
* `lookback_pos`: for `n ≥ 17` the lookback index is at least `1`, so no seed is read after
  `n = 16`. `lookback_nonpos_iff` lists the seven `n` that do read a seed.
* `exists_isP312` and `isP312_unique`: give only the seeds `f[-3..0] = 1`, with no padding. Then the
  recursion is total and determines `f` uniquely. This is the analogue, settled for P312, of the
  open totality question for Hofstadter's Q.

The proof is an induction on `2 f[n] ≤ n + 20` (`two_mul_f_le`). Its base cases `n ≤ 19` are the
computed values `f_1`, …, `f_19`.
-/

namespace Ruliology.NumberSystems
namespace P312

/-- P312 with Wolfram's padding. The result carries the bound `1 ≤ f n`, which makes the
recursion visibly well-founded. -/
def fAux (n : Int) : {v : Nat // 1 ≤ v} :=
  if h : n ≤ 0 then ⟨1, Nat.le_refl 1⟩
  else
    match fAux (n - 2) with
    | ⟨v, hv⟩ => ⟨3 + (fAux (n - v)).1, by omega⟩
termination_by n.toNat
decreasing_by all_goals omega

/-- Wolfram's P312: `f[n] = 1` for `n ≤ 0`, and `f[n] = 3 + f[n - f[n - 2]]` otherwise. -/
def f (n : Int) : Nat := (fAux n).1

theorem one_le_f (n : Int) : 1 ≤ f n := (fAux n).2

/-- Defining equation: the padding. -/
theorem f_eq_one_of_nonpos {n : Int} (h : n ≤ 0) : f n = 1 := by
  show (fAux n).1 = 1
  rw [fAux, dif_pos h]

/-- Defining equation: the recursion. -/
theorem f_eq_of_pos {n : Int} (h : 0 < n) : f n = 3 + f (n - f (n - 2)) := by
  show (fAux n).1 = 3 + (fAux (n - (fAux (n - 2)).1)).1
  conv => lhs; rw [fAux, dif_neg (show ¬ n ≤ 0 by omega)]

theorem four_le_f {n : Int} (h : 1 ≤ n) : 4 ≤ f n := by
  rw [f_eq_of_pos (by omega)]
  have := one_le_f (n - f (n - 2))
  omega

/-! ### Computed values -/

theorem f_eval {n m₂ m : Int} {a b : Nat} (hn : 0 < n) (h₂ : n - 2 = m₂) (ha : f m₂ = a)
    (h : n - a = m) (hb : f m = b) : f n = 3 + b := by
  rw [f_eq_of_pos hn, h₂, ha, h, hb]

theorem f_neg_one : f (-1) = 1 := f_eq_one_of_nonpos (by decide)
theorem f_zero : f 0 = 1 := f_eq_one_of_nonpos (by decide)

theorem f_1 : f 1 = 4 :=
  f_eval (n := 1) (m₂ := -1) (a := 1) (m := 0) (b := 1) (by decide) (by decide)
    (f_eq_one_of_nonpos (by decide : (-1 : Int) ≤ 0)) (by decide)
    (f_eq_one_of_nonpos (by decide : (0 : Int) ≤ 0))
theorem f_2 : f 2 = 7 :=
  f_eval (n := 2) (m₂ := 0) (a := 1) (m := 1) (b := 4) (by decide) (by decide)
    (f_eq_one_of_nonpos (by decide : (0 : Int) ≤ 0)) (by decide) f_1
theorem f_3 : f 3 = 4 :=
  f_eval (n := 3) (m₂ := 1) (a := 4) (m := -1) (b := 1) (by decide) (by decide) f_1 (by decide)
    (f_eq_one_of_nonpos (by decide : (-1 : Int) ≤ 0))
theorem f_4 : f 4 = 4 :=
  f_eval (n := 4) (m₂ := 2) (a := 7) (m := -3) (b := 1) (by decide) (by decide) f_2 (by decide)
    (f_eq_one_of_nonpos (by decide : (-3 : Int) ≤ 0))
theorem f_5 : f 5 = 7 :=
  f_eval (n := 5) (m₂ := 3) (a := 4) (m := 1) (b := 4) (by decide) (by decide) f_3 (by decide) f_1
theorem f_6 : f 6 = 10 :=
  f_eval (n := 6) (m₂ := 4) (a := 4) (m := 2) (b := 7) (by decide) (by decide) f_4 (by decide) f_2
theorem f_7 : f 7 = 4 :=
  f_eval (n := 7) (m₂ := 5) (a := 7) (m := 0) (b := 1) (by decide) (by decide) f_5 (by decide)
    (f_eq_one_of_nonpos (by decide : (0 : Int) ≤ 0))
theorem f_8 : f 8 = 4 :=
  f_eval (n := 8) (m₂ := 6) (a := 10) (m := -2) (b := 1) (by decide) (by decide) f_6 (by decide)
    (f_eq_one_of_nonpos (by decide : (-2 : Int) ≤ 0))
theorem f_9 : f 9 = 10 :=
  f_eval (n := 9) (m₂ := 7) (a := 4) (m := 5) (b := 7) (by decide) (by decide) f_7 (by decide) f_5
theorem f_10 : f 10 = 13 :=
  f_eval (n := 10) (m₂ := 8) (a := 4) (m := 6) (b := 10) (by decide) (by decide) f_8 (by decide)
    f_6
theorem f_11 : f 11 = 7 :=
  f_eval (n := 11) (m₂ := 9) (a := 10) (m := 1) (b := 4) (by decide) (by decide) f_9 (by decide)
    f_1
theorem f_12 : f 12 = 4 :=
  f_eval (n := 12) (m₂ := 10) (a := 13) (m := -1) (b := 1) (by decide) (by decide) f_10
    (by decide) (f_eq_one_of_nonpos (by decide : (-1 : Int) ≤ 0))
theorem f_13 : f 13 = 13 :=
  f_eval (n := 13) (m₂ := 11) (a := 7) (m := 6) (b := 10) (by decide) (by decide) f_11
    (by decide) f_6
theorem f_14 : f 14 = 16 :=
  f_eval (n := 14) (m₂ := 12) (a := 4) (m := 10) (b := 13) (by decide) (by decide) f_12
    (by decide) f_10
theorem f_15 : f 15 = 10 :=
  f_eval (n := 15) (m₂ := 13) (a := 13) (m := 2) (b := 7) (by decide) (by decide) f_13
    (by decide) f_2
theorem f_16 : f 16 = 4 :=
  f_eval (n := 16) (m₂ := 14) (a := 16) (m := 0) (b := 1) (by decide) (by decide) f_14
    (by decide) (f_eq_one_of_nonpos (by decide : (0 : Int) ≤ 0))
theorem f_17 : f 17 = 7 :=
  f_eval (n := 17) (m₂ := 15) (a := 10) (m := 7) (b := 4) (by decide) (by decide) f_15
    (by decide) f_7
theorem f_18 : f 18 = 19 :=
  f_eval (n := 18) (m₂ := 16) (a := 4) (m := 14) (b := 16) (by decide) (by decide) f_16
    (by decide) f_14
theorem f_19 : f 19 = 7 :=
  f_eval (n := 19) (m₂ := 17) (a := 7) (m := 12) (b := 4) (by decide) (by decide) f_17
    (by decide) f_12

/-! ### The inductive invariant -/

theorem invariant_base {n : Int} (h₁ : 1 ≤ n) (h₂ : n ≤ 19) :
    2 * (f n : Int) ≤ n + 20 ∧ (17 ≤ n → 1 ≤ n - f (n - 2) ∧ 7 ≤ f n) := by
  have : n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 ∨ n = 9 ∨ n = 10 ∨
      n = 11 ∨ n = 12 ∨ n = 13 ∨ n = 14 ∨ n = 15 ∨ n = 16 ∨ n = 17 ∨ n = 18 ∨ n = 19 := by
    omega
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [f_1, f_2, f_3, f_4, f_5, f_6, f_7, f_8, f_9, f_10, f_11, f_12, f_13, f_14, f_15, f_16,
      f_17, f_18, f_19] <;> omega

/-- For `1 ≤ n ≤ k`: `2 f[n] ≤ n + 20`. For `n ≥ 17` also: the lookback index is at least `1`,
and `f[n] ≥ 7`. -/
theorem invariant : ∀ k : Nat, ∀ n : Int, 1 ≤ n → n ≤ k →
    2 * (f n : Int) ≤ n + 20 ∧ (17 ≤ n → 1 ≤ n - f (n - 2) ∧ 7 ≤ f n)
  | 0, n, h₁, h₂ => absurd h₂ (by omega)
  | k + 1, n, h₁, h₂ => by
    by_cases hk : n ≤ k
    · exact invariant k n h₁ hk
    by_cases hsmall : n ≤ 19
    · exact invariant_base h₁ hsmall
    have ih₂ := invariant k (n - 2) (by omega) (by omega)
    have hlb : 1 ≤ n - f (n - 2) := by omega
    have h₇ : 7 ≤ f (n - 2) := (ih₂.2 (by omega)).2
    have hpos := one_le_f (n - 2)
    have ihj := invariant k (n - f (n - 2)) hlb (by omega)
    have hfn := f_eq_of_pos (n := n) (by omega)
    have h₄ := four_le_f hlb
    exact ⟨by omega, fun _ => ⟨hlb, by omega⟩⟩

theorem invariant' {n : Int} (h : 1 ≤ n) :
    2 * (f n : Int) ≤ n + 20 ∧ (17 ≤ n → 1 ≤ n - f (n - 2) ∧ 7 ≤ f n) :=
  invariant n.toNat n h (by omega)

/-! ### Main results -/

/-- `2 f[n] ≤ n + 20` for all `n ≥ 1`. The bound is attained at `n = 18`. -/
theorem two_mul_f_le {n : Int} (h : 1 ≤ n) : 2 * (f n : Int) ≤ n + 20 := (invariant' h).1

/-- `f[n] ≥ 7` for all `n ≥ 17`. -/
theorem seven_le_f {n : Int} (h : 17 ≤ n) : 7 ≤ f n := ((invariant' (by omega)).2 h).2

/-- For `n ≥ 17` the lookback index `n - f[n-2]` is at least `1`, so no seed is ever read again. -/
theorem lookback_pos {n : Int} (h : 17 ≤ n) : 1 ≤ n - f (n - 2) :=
  ((invariant' (by omega)).2 h).1

/-- **Main theorem.** P312 only ever looks back as far as `f[-3]`. -/
theorem lookback_ge_neg_three {n : Int} (h : 1 ≤ n) : -3 ≤ n - f (n - 2) := by
  by_cases h17 : 17 ≤ n
  · have := lookback_pos h17
    omega
  have : n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 ∨ n = 9 ∨ n = 10 ∨
      n = 11 ∨ n = 12 ∨ n = 13 ∨ n = 14 ∨ n = 15 ∨ n = 16 := by
    omega
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl <;>
    simp [f_neg_one, f_zero, f_1, f_2, f_3, f_4, f_5, f_6, f_7, f_8, f_9, f_10, f_11, f_12,
      f_13, f_14] <;> omega

/-- The bound is attained: at `n = 4` the lookback index is exactly `-3`. -/
theorem lookback_four : (4 : Int) - f (4 - 2) = -3 := by
  simp [f_2]

/-- Exactly seven values of `n` read a seed, i.e. have lookback index `≤ 0`. -/
theorem lookback_nonpos_iff {n : Int} (h : 1 ≤ n) :
    n - f (n - 2) ≤ 0 ↔ n = 1 ∨ n = 3 ∨ n = 4 ∨ n = 7 ∨ n = 8 ∨ n = 12 ∨ n = 16 := by
  by_cases h17 : 17 ≤ n
  · have := lookback_pos h17
    constructor <;> intro <;> omega
  have : n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 ∨ n = 9 ∨ n = 10 ∨
      n = 11 ∨ n = 12 ∨ n = 13 ∨ n = 14 ∨ n = 15 ∨ n = 16 := by
    omega
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl <;>
    simp [f_neg_one, f_zero, f_1, f_2, f_3, f_4, f_5, f_6, f_7, f_8, f_9, f_10, f_11, f_12,
      f_13, f_14]

/-! ### Totality without padding -/

/-- `g` satisfies P312 with only the seeds `g (-3) = ⋯ = g 0 = 1` and no padding. Every lookback
must land in `[-3, n - 1]`, mirroring Hofstadter's partial semantics for his Q-sequence. -/
def IsP312 (g : Int → Nat) : Prop :=
  (∀ n, -3 ≤ n → n ≤ 0 → g n = 1) ∧
  ∀ n, 1 ≤ n → -3 ≤ n - g (n - 2) ∧ g n = 3 + g (n - g (n - 2))

theorem isP312_f : IsP312 f :=
  ⟨fun _ _ h => f_eq_one_of_nonpos h,
    fun _ h => ⟨lookback_ge_neg_three h, f_eq_of_pos (by omega)⟩⟩

/-- **Totality.** The seeds `f[-3..0]` alone define P312 at every `n`: the partial recursion never
dies. -/
theorem exists_isP312 : ∃ g, IsP312 g := ⟨f, isP312_f⟩

theorem IsP312.one_le {g : Int → Nat} (hg : IsP312 g) {n : Int} (h : -3 ≤ n) : 1 ≤ g n := by
  by_cases hn : n ≤ 0
  · rw [hg.1 n h hn]
    exact Nat.le_refl 1
  · rw [(hg.2 n (by omega)).2]
    omega

/-- **Uniqueness.** The seeds determine the function on `[-3, ∞)`. -/
theorem isP312_unique {g h : Int → Nat} (hg : IsP312 g) (hh : IsP312 h) :
    ∀ n, -3 ≤ n → g n = h n := by
  suffices H : ∀ k : Nat, ∀ n : Int, -3 ≤ n → n < (k : Int) - 3 → g n = h n from
    fun n hn => H (n + 4).toNat n hn (by omega)
  intro k
  induction k with
  | zero => intro n h₁ h₂; omega
  | succ k ih =>
    intro n h₁ h₂
    by_cases hlt : n < (k : Int) - 3
    · exact ih n h₁ hlt
    by_cases hn : n ≤ 0
    · rw [hg.1 n h₁ hn, hh.1 n h₁ hn]
    have hgn := hg.2 n (by omega)
    have hhn := hh.2 n (by omega)
    have e₂ : g (n - 2) = h (n - 2) := ih (n - 2) (by omega) (by omega)
    have hpos := hg.one_le (n := n - 2) (by omega)
    have ej : g (n - g (n - 2)) = h (n - g (n - 2)) := ih _ hgn.1 (by omega)
    rw [hgn.2, hhn.2, ← e₂, ej]

/-! ### A fast table for cross-validation

The compiled `f` recomputes subterms, so its running time grows exponentially. `fList n`
computes `[f 1, …, f n]` bottom-up in `O(n²)`, and `fList_getD` proves that it agrees with `f`. -/

/-- Read `f m` from a table `t = [f 1, …, f t.length]`, with the padding value `1` for `m ≤ 0`. -/
def lookup (t : List Nat) (m : Int) : Nat := if m ≤ 0 then 1 else t.getD (m.toNat - 1) 1

/-- The next value `f (t.length + 1)`, computed from the table `t`. -/
def nextVal (t : List Nat) : Nat :=
  let m : Int := t.length + 1
  3 + lookup t (m - lookup t (m - 2))

/-- `fList n = [f 1, …, f n]`. -/
def fList : Nat → List Nat
  | 0 => []
  | n + 1 => let t := fList n; t ++ [nextVal t]

theorem length_fList (n : Nat) : (fList n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [fList, ih]

theorem lookup_eq {t : List Nat} (ht : ∀ k, k < t.length → t.getD k 1 = f (k + 1)) {m : Int}
    (hm : m ≤ t.length) : lookup t m = f m := by
  unfold lookup
  by_cases h₀ : m ≤ 0
  · rw [if_pos h₀, f_eq_one_of_nonpos h₀]
  · rw [if_neg h₀, ht _ (by omega)]
    congr 1
    omega

theorem nextVal_eq {t : List Nat} (ht : ∀ k, k < t.length → t.getD k 1 = f (k + 1)) :
    nextVal t = f (t.length + 1) := by
  unfold nextVal
  simp only
  rw [lookup_eq ht (m := (t.length : Int) + 1 - 2) (by omega)]
  have hpos := one_le_f ((t.length : Int) + 1 - 2)
  rw [lookup_eq ht (by omega), f_eq_of_pos (n := (t.length : Int) + 1) (by omega)]

/-- **Table correctness.** Entry `k` of `fList n` is `f (k + 1)`. -/
theorem fList_getD (n : Nat) : ∀ k, k < n → (fList n).getD k 1 = f (k + 1) := by
  induction n with
  | zero => intro k hk; omega
  | succ n ih =>
    intro k hk
    have ht : ∀ k, k < (fList n).length → (fList n).getD k 1 = f (k + 1) := by
      rw [length_fList]; exact ih
    show (fList n ++ [nextVal (fList n)]).getD k 1 = f (k + 1)
    rw [List.getD_eq_getElem?_getD]
    by_cases hkn : k < n
    · rw [List.getElem?_append_left (by rw [length_fList]; exact hkn),
        ← List.getD_eq_getElem?_getD]
      exact ih k hkn
    · have hk' : k = n := by omega
      subst hk'
      have h := @List.getElem?_concat_length _ (fList k) (nextVal (fList k))
      rw [length_fList] at h
      rw [h, Option.getD_some, nextVal_eq ht, length_fList]

theorem fList_getElem (n k : Nat) (h : k < (fList n).length) : (fList n)[k] = f (k + 1) := by
  rw [← fList_getD n k (by rw [length_fList] at h; exact h)]
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

example : fList 19 = [4, 7, 4, 4, 7, 10, 4, 4, 10, 13, 7, 4, 13, 16, 10, 4, 7, 19, 7] := by decide

/-! Cross-validation vectors: `f[n]` for `n = 1, …, 19` (the WL table). -/

example : [f 1, f 2, f 3, f 4, f 5, f 6, f 7, f 8, f 9, f 10] =
    [4, 7, 4, 4, 7, 10, 4, 4, 10, 13] := by
  simp [f_1, f_2, f_3, f_4, f_5, f_6, f_7, f_8, f_9, f_10]

end P312
end Ruliology.NumberSystems
