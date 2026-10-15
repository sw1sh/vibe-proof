import Ruliology.CellularAutomata.Rule30PeriodTwo

/-!
# Program A: the zero-boundary left half (ZBL) and the period-2 question Q_01

Positions are indexed by `i : Nat`, where `i` stands for the cell at position `-(i+1)`;
the wall (position `0`) is always white.  One ZBL step (`zstep`) is rule 30 on `p ≤ -1` with
column `0` held white; `zorb x t` is the row at time `t`.

Contents (all proved, standard axioms only):
* backward determinism at forced steps (`backward_det`, `history_det`), the backward transducer
  `back` and the finite-preimage criterion `back_fin_iff`;
* light cone, `pivot` (left permutivity along anti-diagonals), zero-run localization
  `zero_run_local`, near-wall completion `complete_near_wall`, `far_light_cone` and the
  edge-region barrier `edge_region_barrier`;
* the forced skeleton of a constrained history: `survive_iff`, `col2_doubling`, `col3_of_col2`,
  `no_two_white`;
* realization bijection (`realization`): column `-1` determines the row; Q_01 is equivalent to
  "the forced left half `lam (alt f)` is never finite" (`Q01_iff_LR`) and to bounded white runs
  of the forced row (`Q01_iff_bounded`, via compactness `uniform_death`); the constrained
  two-step dynamics is the full shift on the free bits (`two_step_shift`);
* Jen with a clock for the ZBL (`jen_clock`, `col_not_eventually_periodic`, `free_bits_clock`);
* bridges: `no_eventual_period_two` (Q_01 excludes period 2), `alternating_free_bits_clock` and
  `alternating_right_col1_clock` (under an alternating center the free bits / right column 1 at
  white times cannot be periodic on long windows), `Q01_iff_staged` (this `Q01` is the staged
  `Rule30PeriodTwo.Q01`).
Q_01 itself is NOT proved here.
-/

namespace R30ProgA
open Ruliology.CellularAutomata.Rule30Jen

/-- right neighbour of index `i` (the wall for `i = 0`) -/
def rn (x : Nat → Bool) : Nat → Bool
  | 0 => false
  | j + 1 => x j

/-- one ZBL step -/
def zstep (x : Nat → Bool) (i : Nat) : Bool := xor (x (i + 1)) (x i || rn x i)

/-- ZBL orbit -/
def zorb (x : Nat → Bool) : Nat → Nat → Bool
  | 0 => x
  | t + 1 => zstep (zorb x t)

/-- a row is finite (white from index `m` on) -/
def Fin0 (x : Nat → Bool) : Prop := ∃ m, ∀ i, m ≤ i → x i = false

theorem zorb_succ (x : Nat → Bool) (t : Nat) : zorb x (t + 1) = zstep (zorb x t) := rfl

theorem zorb_add (x : Nat → Bool) (t u : Nat) : zorb (zorb x t) u = zorb x (t + u) := by
  induction u with
  | zero => rfl
  | succ u ih => rw [zorb_succ, ih, ← Nat.add_assoc, zorb_succ]

theorem zstep_zero (x : Nat → Bool) : zstep x 0 = xor (x 1) (x 0) := by
  simp [zstep, rn]

theorem zstep_succ (x : Nat → Bool) (j : Nat) :
    zstep x (j + 1) = xor (x (j + 2)) (x (j + 1) || x j) := rfl

/-- left permutivity: the cell one further from the wall is recovered from the next row -/
theorem left_perm (x : Nat → Bool) (i : Nat) :
    x (i + 1) = xor (zstep x i) (x i || rn x i) := by
  unfold zstep
  cases x (i + 1) <;> cases (x i || rn x i) <;> rfl

/-- **Backward determinism.** Two half-line rows with the same image and the same cell next to the
wall are equal.  In a constrained history the cell next to the wall is forced (black) at every
other step, so the dynamics is backward deterministic at those steps. -/
theorem backward_det {x y : Nat → Bool} (h : zstep x = zstep y) (h0 : x 0 = y 0) : x = y := by
  have key : ∀ n, x n = y n ∧ x (n + 1) = y (n + 1) := by
    intro n
    induction n with
    | zero =>
      refine ⟨h0, ?_⟩
      rw [left_perm x 0, left_perm y 0, h, h0]
      rfl
    | succ n ih =>
      refine ⟨ih.2, ?_⟩
      rw [left_perm x (n + 1), left_perm y (n + 1), h, ih.2]
      show xor (zstep y (n + 1)) (y (n + 1) || x n) = xor (zstep y (n + 1)) (y (n + 1) || y n)
      rw [ih.1]
  funext n
  exact (key n).1

/-- **History from the final row.**  A history is determined by its row at time `T` together with
the cells next to the wall at times `< T` (in a constrained history these are forced at every
other step, so only the free bits are needed). -/
theorem history_det {x y : Nat → Bool} {T : Nat} (hT : zorb x T = zorb y T)
    (h0 : ∀ t, t < T → zorb x t 0 = zorb y t 0) : ∀ t, t ≤ T → zorb x t = zorb y t := by
  have key : ∀ n, n ≤ T → zorb x (T - n) = zorb y (T - n) := by
    intro n
    induction n with
    | zero => intro _; simpa using hT
    | succ n ih =>
      intro hn
      apply backward_det
      · rw [← zorb_succ, ← zorb_succ, show T - (n + 1) + 1 = T - n by omega]
        exact ih (by omega)
      · exact h0 _ (by omega)
  intro t ht
  have := key (T - t) (by omega)
  rwa [show T - (T - t) = t by omega] at this

/-- the unique preimage with prescribed cell `b` next to the wall (backward transducer) -/
def back (b : Bool) (y : Nat → Bool) : Nat → Bool
  | 0 => b
  | 1 => xor (y 0) b
  | j + 2 => xor (y (j + 1)) (back b y (j + 1) || back b y j)

theorem zstep_back (b : Bool) (y : Nat → Bool) : zstep (back b y) = y := by
  funext i
  cases i with
  | zero =>
    rw [zstep_zero]
    show xor (xor (y 0) b) b = y 0
    cases y 0 <;> cases b <;> rfl
  | succ j =>
    rw [zstep_succ]
    show xor (xor (y (j + 1)) (back b y (j + 1) || back b y j)) (back b y (j + 1) || back b y j) = y (j + 1)
    cases y (j + 1) <;> cases (back b y (j + 1) || back b y j) <;> rfl

theorem preimage_eq_back {x y : Nat → Bool} (h : zstep x = y) : x = back (x 0) y :=
  backward_det (by rw [zstep_back, h]) rfl

/-- **Finite-preimage criterion.**  If `y` is white from index `n ≥ 1` on, its preimage with cell `b`
next to the wall is finite iff the backward transducer is in state `(white, white)` at indices
`n - 1, n`. -/
theorem back_fin_iff (b : Bool) {y : Nat → Bool} {n : Nat} (hn : 1 ≤ n)
    (hy : ∀ i, n ≤ i → y i = false) :
    Fin0 (back b y) ↔ (back b y (n - 1) = false ∧ back b y n = false) := by
  constructor
  · rintro ⟨M, hM⟩
    -- if one of the two is black, every later cell is black
    have prop : ∀ k, (back b y (n - 1 + k) || back b y (n + k)) = true → back b y (n + k + 1) = true := by
      intro k hk
      rw [show n + k + 1 = (n + k - 1) + 2 by omega, back, hy _ (by omega),
        show n + k - 1 + 1 = n + k by omega, show n + k - 1 = n - 1 + k by omega]
      rw [Bool.or_comm] at hk
      simp [hk]
    refine Classical.byContradiction fun hne => ?_
    have h0 : (back b y (n - 1 + 0) || back b y (n + 0)) = true := by
      cases h1 : back b y (n - 1) <;> cases h2 : back b y n <;> simp_all
    have allb : ∀ k, back b y (n + k + 1) = true := by
      intro k
      induction k with
      | zero => exact prop 0 h0
      | succ k ih =>
        apply prop (k + 1)
        simp [show n + (k + 1) = n + k + 1 by omega, ih]
    have := allb M
    rw [hM _ (by omega)] at this
    exact absurd this (by decide)
  · rintro ⟨h1, h2⟩
    refine ⟨n - 1, fun i hi => ?_⟩
    have all : ∀ k, back b y (n - 1 + k) = false ∧ back b y (n + k) = false := by
      intro k
      induction k with
      | zero => exact ⟨h1, h2⟩
      | succ k ih =>
        refine ⟨by rw [show n - 1 + (k + 1) = n + k by omega]; exact ih.2, ?_⟩
        rw [show n + (k + 1) = (n - 1 + k) + 2 by omega, back, hy _ (by omega),
          show n - 1 + k + 1 = n + k by omega, ih.2, ih.1]
        rfl
    have := (all (i - (n - 1))).1
    rwa [show n - 1 + (i - (n - 1)) = i by omega] at this

/-! ## Finiteness: the left edge moves one cell per step -/

theorem zstep_fin {x : Nat → Bool} {m : Nat} (h : ∀ i, m ≤ i → x i = false) :
    ∀ i, m + 1 ≤ i → zstep x i = false := by
  intro i hi
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  rw [zstep_succ, h (j + 2) (by omega), h (j + 1) (by omega), h j (by omega)]
  rfl

theorem zorb_fin {x : Nat → Bool} {m : Nat} (h : ∀ i, m ≤ i → x i = false) :
    ∀ t i, m + t ≤ i → zorb x t i = false := by
  intro t
  induction t with
  | zero => intro i hi; exact h i (by omega)
  | succ t ih =>
    intro i hi
    exact zstep_fin (m := m + t) ih i (by omega)

/-- the leftmost black cell moves one step per time step -/
theorem zorb_edge {x : Nat → Bool} {m : Nat} (h : ∀ i, m + 1 ≤ i → x i = false)
    (hm : x m = true) : ∀ t, zorb x t (m + t) = true := by
  intro t
  induction t with
  | zero => exact hm
  | succ t ih =>
    rw [zorb_succ, show m + (t + 1) = (m + t) + 1 by omega, zstep_succ, ih,
      zorb_fin h t (m + t + 2) (by omega)]
    cases (zorb x t (m + t + 1)) <;> rfl

/-! ## The light cone -/

/-- cells at distance `< m - t` from the wall at time `t` only depend on the first `m` cells at
time `0` -/
theorem light_cone {x y : Nat → Bool} {m : Nat} (h : ∀ i, i < m → x i = y i) :
    ∀ t i, i + t < m → zorb x t i = zorb y t i := by
  intro t
  induction t with
  | zero => intro i hi; exact h i (by omega)
  | succ t ih =>
    intro i hi
    show zstep (zorb x t) i = zstep (zorb y t) i
    cases i with
    | zero =>
      rw [zstep_zero, zstep_zero, ih 1 (by omega), ih 0 (by omega)]
    | succ j =>
      rw [zstep_succ, zstep_succ, ih (j + 2) (by omega), ih (j + 1) (by omega), ih j (by omega)]

/-- column `-1` up to time `m - 1` only depends on the first `m` cells -/
theorem col_light_cone {x y : Nat → Bool} {m : Nat} (h : ∀ i, i < m → x i = y i) :
    ∀ t, t < m → zorb x t 0 = zorb y t 0 :=
  fun t ht => light_cone h t 0 (by omega)

/-- truncation of a row to its first `d` cells -/
def trunc (x : Nat → Bool) (d : Nat) (i : Nat) : Bool := if i < d then x i else false

/-- **Zero-run localization.**  If the row is white on `[d, d + L)` then column `-1` agrees with
that of the truncated (finite, support `≤ d`) row up to time `d + L - 1`. -/
theorem zero_run_local {x : Nat → Bool} {d L : Nat} (hz : ∀ i, d ≤ i → i < d + L → x i = false) :
    ∀ t, t < d + L → zorb x t 0 = zorb (trunc x d) t 0 := by
  apply col_light_cone
  intro i hi
  unfold trunc
  by_cases hid : i < d
  · rw [if_pos hid]
  · rw [if_neg hid, hz i (by omega) hi]

/-- **Pivot (left permutivity along the anti-diagonal).**  Two rows that agree on `[0, t)` and
differ at `t` have different cells next to the wall at time `t`. -/
theorem pivot {x y : Nat → Bool} {t : Nat} (hagree : ∀ i, i < t → x i = y i) (hdiff : x t ≠ y t) :
    zorb x t 0 ≠ zorb y t 0 := by
  have key : ∀ s, s ≤ t → (∀ i, i < t - s → zorb x s i = zorb y s i) ∧ zorb x s (t - s) ≠ zorb y s (t - s) := by
    intro s
    induction s with
    | zero => intro _; exact ⟨fun i hi => hagree i (by omega), by simpa using hdiff⟩
    | succ s ih =>
      intro hs
      obtain ⟨ha, hd⟩ := ih (by omega)
      refine ⟨fun i hi => ?_, ?_⟩
      · rw [zorb_succ, zorb_succ]
        cases i with
        | zero => rw [zstep_zero, zstep_zero, ha 1 (by omega), ha 0 (by omega)]
        | succ j => rw [zstep_succ, zstep_succ, ha (j + 2) (by omega), ha (j + 1) (by omega), ha j (by omega)]
      · rw [zorb_succ, zorb_succ]
        obtain ⟨u, hu⟩ : ∃ u, t - s = u + 1 := ⟨t - s - 1, by omega⟩
        rw [show t - (s + 1) = u by omega]
        rw [hu] at hd
        unfold zstep
        have hrn : rn (zorb x s) u = rn (zorb y s) u := by
          cases u with
          | zero => rfl
          | succ v => exact ha v (by omega)
        rw [ha u (by omega), hrn]
        intro h
        apply hd
        have xor_cancel : ∀ a b o : Bool, xor a o = xor b o → a = b := by decide
        exact xor_cancel _ _ _ h
  have := (key t (Nat.le_refl t)).2
  simpa using this

/-- **Near-wall completion (realization barrier).**  Any far part `z` (on indices `≥ d`) can be
completed on `[0, d)` so that the cell next to the wall follows any prescribed values up to time
`d - 1`.  The left diagonals of the far part (which never feel the near part) are therefore
compatible with any constraint on the time window `[0, d)`. -/
theorem complete_near_wall (z : Nat → Bool) (c : Nat → Bool) :
    ∀ d, ∃ x : Nat → Bool, (∀ i, d ≤ i → x i = z i) ∧ ∀ t, t < d → zorb x t 0 = c t := by
  intro d
  induction d with
  | zero => exact ⟨z, fun _ _ => rfl, fun t ht => absurd ht (by omega)⟩
  | succ d ih =>
    obtain ⟨x, hxz, hxc⟩ := ih
    by_cases hok : zorb x d 0 = c d
    · exact ⟨x, fun i hi => hxz i (by omega), fun t ht => by
        by_cases htd : t = d
        · subst htd; exact hok
        · exact hxc t (by omega)⟩
    · let x' : Nat → Bool := fun i => if i = d then !x d else x i
      have hagree : ∀ i, i < d → x' i = x i := fun i hi => by simp [x', show i ≠ d by omega]
      have hdiff : x' d ≠ x d := by simp [x']
      have hflip := pivot hagree hdiff
      refine ⟨x', fun i hi => ?_, fun t ht => ?_⟩
      · simp [x', show i ≠ d by omega]; exact hxz i (by omega)
      · by_cases htd : t = d
        · subst htd
          revert hflip hok
          cases zorb x' t 0 <;> cases zorb x t 0 <;> cases c t <;> simp
        · rw [col_light_cone (m := d) (fun i hi => hagree i hi) t (by omega)]
          exact hxc t (by omega)

/-- the near part's influence spreads away from the wall at most one cell per step: rows that
agree from index `d` on agree from index `d + t` on at time `t` -/
theorem far_light_cone {x y : Nat → Bool} {d : Nat} (h : ∀ i, d ≤ i → x i = y i) :
    ∀ t i, d + t ≤ i → zorb x t i = zorb y t i := by
  intro t
  induction t with
  | zero => intro i hi; exact h i (by omega)
  | succ t ih =>
    intro i hi
    rw [zorb_succ, zorb_succ]
    obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    rw [zstep_succ, zstep_succ, ih (j + 2) (by omega), ih (j + 1) (by omega), ih j (by omega)]

/-- **Edge-region barrier.**  Fix any far part `z` with leftmost black cell at index `m - 1` and any
prescribed values `c` of the cell next to the wall.  For every `d ≤ m` there is a row that agrees
with `z` from index `d` on (so its left-edge region of width `m - d` coincides with that of `z` at
every time, including all eventually periodic left diagonals there) and whose cell next to the wall
follows `c` up to time `d - 1`.  So no contradiction can be derived from the left-edge structure
together with the wall constraint on a time window shorter than the distance from the wall to the
part of the edge structure being used. -/
theorem edge_region_barrier (z c : Nat → Bool) (d : Nat) :
    ∃ x : Nat → Bool, (∀ i, d ≤ i → x i = z i) ∧ (∀ t, t < d → zorb x t 0 = c t) ∧
      ∀ t i, d + t ≤ i → zorb x t i = zorb z t i := by
  obtain ⟨x, hxz, hxc⟩ := complete_near_wall z c d
  exact ⟨x, hxz, hxc, far_light_cone hxz⟩

/-! ## Constrained histories -/

/-- the forced cell next to the wall in two steps -/
theorem zorb_two_zero (x : Nat → Bool) (h0 : x 0 = true) : zorb x 2 0 = xor (x 1) (x 2) := by
  show zstep (zstep x) 0 = xor (x 1) (x 2)
  rw [zstep_zero, zstep_zero, zstep_succ, h0]
  cases x 1 <;> cases x 2 <;> rfl

/-- **One-step survival criterion.**  At a forced (black) step, the next forced step is black iff
the second and third cells differ. -/
theorem survive_iff (x : Nat → Bool) (h0 : x 0 = true) : zorb x 2 0 = true ↔ x 1 ≠ x 2 := by
  rw [zorb_two_zero x h0]
  cases x 1 <;> cases x 2 <;> decide

/-- column `-2` is constant on each forced pair of steps -/
theorem col2_doubling (x : Nat → Bool) (h0 : x 0 = true) (h2 : zorb x 2 0 = true) :
    zstep x 1 = x 1 := by
  have hne := (survive_iff x h0).1 h2
  rw [zstep_succ, h0]
  cases h1 : x 1 <;> cases h2' : x 2 <;> simp_all

/-- column `-3` is the complement of column `-2` one step later whenever columns `-1, -2` are not
both white -/
theorem col3_of_col2 (x : Nat → Bool) (h : (x 0 || x 1) = true) : x 2 = !zstep x 1 := by
  rw [zstep_succ]
  revert h
  cases x 0 <;> cases x 1 <;> cases x 2 <;> decide

/-- the no-`00` property of constrained histories (both steps of a forced pair) -/
theorem no_two_white (x : Nat → Bool) (h0 : x 0 = true) (h2 : zorb x 2 0 = true) :
    (x 0 || x 1) = true ∧ (zstep x 0 || zstep x 1) = true := by
  have hne := (survive_iff x h0).1 h2
  refine ⟨by rw [h0]; rfl, ?_⟩
  rw [zstep_zero, zstep_succ, h0]
  cases h1 : x 1 <;> cases h2' : x 2 <;> simp_all


/-! ## Realization: column `-1` determines the whole history (sideways construction) -/

/-- sideways columns built from column `-1` (= `a`) and the white wall: `cols a k t` is the cell at
position `-k`, time `t` -/
def cols (a : Nat → Bool) : Nat → Nat → Bool
  | 0, _ => false
  | 1, t => a t
  | k + 2, t => xor (cols a (k + 1) (t + 1)) (cols a (k + 1) t || cols a k t)

/-- the initial row forced by the column-`-1` sequence `a` -/
def lam (a : Nat → Bool) (i : Nat) : Bool := cols a (i + 1) 0

theorem realize (a : Nat → Bool) : ∀ t i, zorb (lam a) t i = cols a (i + 1) t := by
  intro t
  induction t with
  | zero => intro i; rfl
  | succ t ih =>
    intro i
    rw [zorb_succ]
    cases i with
    | zero =>
      rw [zstep_zero, ih 1, ih 0]
      show xor (xor (a (t + 1)) (a t || false)) (a t) = a (t + 1)
      cases a (t + 1) <;> cases a t <;> rfl
    | succ j =>
      rw [zstep_succ, ih (j + 2), ih (j + 1), ih j]
      show xor (xor (cols a (j + 2) (t + 1)) (cols a (j + 2) t || cols a (j + 1) t))
        (cols a (j + 2) t || cols a (j + 1) t) = cols a (j + 2) (t + 1)
      cases cols a (j + 2) (t + 1) <;> cases (cols a (j + 2) t || cols a (j + 1) t) <;> rfl

/-- the history with column `-1` equal to `a` is the sideways construction -/
theorem history_eq_cols {x : Nat → Bool} {a : Nat → Bool} (h : ∀ t, zorb x t 0 = a t) :
    ∀ k t, zorb x t k = cols a (k + 1) t := by
  have key : ∀ k, (∀ t, zorb x t k = cols a (k + 1) t) ∧ (∀ t, zorb x t (k + 1) = cols a (k + 2) t) := by
    intro k
    induction k with
    | zero =>
      refine ⟨fun t => h t, fun t => ?_⟩
      rw [left_perm (zorb x t) 0, ← zorb_succ, h (t + 1), h t]
      rfl
    | succ k ih =>
      refine ⟨ih.2, fun t => ?_⟩
      rw [left_perm (zorb x t) (k + 1), ← zorb_succ, ih.2 (t + 1), ih.2 t]
      show xor (cols a (k + 2) (t + 1)) (cols a (k + 2) t || zorb x t k) = cols a (k + 3) t
      rw [ih.1 t]
      rfl
  exact fun k => (key k).1

/-- **Realization bijection.**  For every column-`-1` sequence `a` there is exactly one ZBL row
whose history has column `-1` equal to `a`, namely `lam a`. -/
theorem realization (a : Nat → Bool) :
    (∀ t, zorb (lam a) t 0 = a t) ∧ ∀ x, (∀ t, zorb x t 0 = a t) → x = lam a := by
  refine ⟨fun t => realize a t 0, fun x h => ?_⟩
  funext i
  have := history_eq_cols h i 0
  exact this

/-! ## Q_01 and its forced-left-half form -/

/-- **Q_01**: no finite ZBL row keeps the cell next to the wall black at every even step. -/
def Q01 : Prop := ∀ x, Fin0 x → ¬ ∀ s, zorb x (2 * s) 0 = true

/-- column `-1` of a constrained history: black at even steps, free bits `f` at odd steps -/
def alt (f : Nat → Bool) (t : Nat) : Bool := if t % 2 = 0 then true else f (t / 2)

/-- **LR** (forced left half form): for every choice of the free bits, the forced row is infinite. -/
def LR : Prop := ∀ f, ¬ Fin0 (lam (alt f))

theorem Q01_iff_LR : Q01 ↔ LR := by
  constructor
  · intro hQ f hfin
    refine hQ _ hfin fun s => ?_
    rw [(realization (alt f)).1]
    simp [alt]
  · intro hL x hfin hc
    let f : Nat → Bool := fun s => zorb x (2 * s + 1) 0
    have hx : ∀ t, zorb x t 0 = alt f t := by
      intro t
      unfold alt
      by_cases ht : t % 2 = 0
      · rw [if_pos ht]
        have := hc (t / 2)
        rwa [show 2 * (t / 2) = t by omega] at this
      · rw [if_neg ht]
        show zorb x t 0 = zorb x (2 * (t / 2) + 1) 0
        rw [show 2 * (t / 2) + 1 = t by omega]
    have := (realization (alt f)).2 x hx
    exact hL f (this ▸ hfin)

/-- **Conjugacy.**  Two ZBL steps of the forced row are the forced row of the shifted free bits:
the constrained two-step dynamics is a full one-sided shift on the free bits. -/
theorem two_step_shift (f : Nat → Bool) :
    zorb (lam (alt f)) 2 = lam (alt (fun s => f (s + 1))) := by
  apply (realization _).2
  intro t
  rw [zorb_add, Nat.add_comm, (realization (alt f)).1]
  unfold alt
  by_cases ht : t % 2 = 0
  · rw [if_pos (by omega), if_pos ht]
  · rw [if_neg (by omega), if_neg ht, show (t + 2) / 2 = t / 2 + 1 by omega]

/-- the phase-1 version of Q_01 follows from Q_01 (apply it one step later) -/
theorem Q01_phase1 (hQ : Q01) : ∀ x, Fin0 x → ¬ ∀ s, zorb x (2 * s + 1) 0 = true := by
  intro x ⟨m, hm⟩ hc
  refine hQ (zstep x) ⟨m + 1, zstep_fin hm⟩ fun s => ?_
  have := hc s
  rw [show 2 * s + 1 = 1 + 2 * s by omega, ← zorb_add] at this
  exact this


/-! ## Q_01 as bounded white runs of the forced row (compactness) -/

/-- the finite row given by a list -/
def ofList (l : List Bool) (i : Nat) : Bool := l.getD i false

theorem ofList_range (x : Nat → Bool) (d : Nat) (hx : ∀ i, d ≤ i → x i = false) :
    ofList ((List.range d).map x) = x := by
  funext i
  unfold ofList
  rw [List.getD_eq_getElem?_getD, List.getElem?_map]
  by_cases h : i < d
  · rw [List.getElem?_range h]; rfl
  · rw [List.getElem?_eq_none (by simp; omega), hx i (by omega)]; rfl

/-- under Q_01, finitely many finite rows die by a common time -/
theorem uniform_death_list (hQ : Q01) : ∀ Ls : List (List Bool), ∃ D, ∀ l ∈ Ls,
    ∃ s, s ≤ D ∧ zorb (ofList l) (2 * s) 0 = false := by
  intro Ls
  induction Ls with
  | nil => exact ⟨0, fun l hl => absurd hl (by simp)⟩
  | cons l Ls ih =>
    obtain ⟨D, hD⟩ := ih
    have hfin : Fin0 (ofList l) := ⟨l.length, fun i hi => by
      unfold ofList; rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; rfl⟩
    have : ∃ s, zorb (ofList l) (2 * s) 0 = false := by
      refine Classical.byContradiction fun hn => hQ _ hfin fun s => ?_
      cases h : zorb (ofList l) (2 * s) 0
      · exact absurd ⟨s, h⟩ hn
      · rfl
    obtain ⟨s₀, hs₀⟩ := this
    refine ⟨max D s₀, fun l' hl' => ?_⟩
    rcases List.mem_cons.1 hl' with rfl | hl'
    · exact ⟨s₀, by omega, hs₀⟩
    · obtain ⟨s, hs, h⟩ := hD l' hl'
      exact ⟨s, by omega, h⟩

/-- **Uniform death.** Under Q_01, for every support bound `d` there is a common time by which
every row supported in `[0, d)` has a white cell next to the wall at an even step. -/
theorem uniform_death (hQ : Q01) (d : Nat) : ∃ D, ∀ x : Nat → Bool, (∀ i, d ≤ i → x i = false) →
    ∃ s, s ≤ D ∧ zorb x (2 * s) 0 = false := by
  obtain ⟨D, hD⟩ := uniform_death_list hQ (allLists d)
  refine ⟨D, fun x hx => ?_⟩
  have hmem : (List.range d).map x ∈ allLists d := by
    have := mem_allLists ((List.range d).map x)
    rwa [List.length_map, List.length_range] at this
  obtain ⟨s, hs, h⟩ := hD _ hmem
  rw [ofList_range x d hx] at h
  exact ⟨s, hs, h⟩

/-- **Q_01 ⟺ bounded white runs of the forced row.**  Q_01 holds iff for every depth `d` there
is a bound `B` such that, for every choice of the free bits `f`, the forced row has a black cell
in `[d, d + B)`.  (The optimal `B` is the maximal constrained survival time over supports `≤ d`,
minus `d`, plus one.) -/
theorem Q01_iff_bounded : Q01 ↔ ∀ d, ∃ B, ∀ f : Nat → Bool, ∃ i, d ≤ i ∧ i < d + B ∧ lam (alt f) i = true := by
  constructor
  · intro hQ d
    obtain ⟨D, hD⟩ := uniform_death hQ d
    refine ⟨2 * D + 2, fun f => Classical.byContradiction fun hn => ?_⟩
    have hz : ∀ i, d ≤ i → i < d + (2 * D + 2) → lam (alt f) i = false := by
      intro i h1 h2
      cases h : lam (alt f) i
      · rfl
      · exact absurd ⟨i, h1, h2, h⟩ hn
    obtain ⟨s, hs, hdead⟩ := hD (trunc (lam (alt f)) d) (fun i hi => by simp [trunc]; omega)
    have := zero_run_local hz (2 * s) (by omega)
    rw [← this, (realization (alt f)).1] at hdead
    simp [alt] at hdead
  · intro hB
    rw [Q01_iff_LR]
    rintro f ⟨M, hM⟩
    obtain ⟨B, hB'⟩ := hB M
    obtain ⟨i, hi1, _, hi3⟩ := hB' f
    rw [hM i hi1] at hi3
    exact absurd hi3 (by decide)

/-! ## Light cone and shift equivariance of the sideways construction -/

/-- `cols a k t` only depends on `a` on `[t, t + k)` -/
theorem cols_local {a b : Nat → Bool} : ∀ k t, (∀ j, j < k → a (t + j) = b (t + j)) →
    cols a k t = cols b k t := by
  have key : ∀ k, (∀ t, (∀ j, j < k → a (t + j) = b (t + j)) → cols a k t = cols b k t) ∧
      (∀ t, (∀ j, j < k + 1 → a (t + j) = b (t + j)) → cols a (k + 1) t = cols b (k + 1) t) := by
    intro k
    induction k with
    | zero =>
      refine ⟨fun t _ => rfl, fun t h => ?_⟩
      have := h 0 (by omega)
      simpa [cols] using this
    | succ k ih =>
      refine ⟨ih.2, fun t h => ?_⟩
      show xor (cols a (k + 1) (t + 1)) (cols a (k + 1) t || cols a k t) =
        xor (cols b (k + 1) (t + 1)) (cols b (k + 1) t || cols b k t)
      rw [ih.2 (t + 1) (fun j hj => by
            have := h (j + 1) (by omega); rwa [show t + (j + 1) = t + 1 + j by omega] at this),
        ih.2 t (fun j hj => h j (by omega)), ih.1 t (fun j hj => h j (by omega))]
  exact fun k t h => (key k).1 t h

/-- shift equivariance: `cols a k (t + P)` is `cols` of the shifted sequence at `t` -/
theorem cols_shift (a : Nat → Bool) (P : Nat) : ∀ k t, cols a k (t + P) = cols (fun s => a (s + P)) k t := by
  have key : ∀ k, (∀ t, cols a k (t + P) = cols (fun s => a (s + P)) k t) ∧
      (∀ t, cols a (k + 1) (t + P) = cols (fun s => a (s + P)) (k + 1) t) := by
    intro k
    induction k with
    | zero => exact ⟨fun t => rfl, fun t => rfl⟩
    | succ k ih =>
      refine ⟨ih.2, fun t => ?_⟩
      show xor (cols a (k + 1) (t + P + 1)) (cols a (k + 1) (t + P) || cols a k (t + P)) =
        xor (cols _ (k + 1) (t + 1)) (cols _ (k + 1) t || cols _ k t)
      rw [show t + P + 1 = (t + 1) + P by omega, ih.2, ih.2, ih.1]
  exact fun k t => (key k).1 t

/-! ## Jen with a clock for the ZBL -/

/-- **Jen with a clock (ZBL).**  Let `x` have its leftmost black cell at index `m - 1`.  If the
column next to the wall is `P`-periodic on the time window `[T, T + L]`, then
`L ≤ T + m + 2P - 2`. -/
theorem jen_clock {x : Nat → Bool} {m : Nat} (hm0 : 0 < m) (hfin : ∀ i, m ≤ i → x i = false)
    (hedge : x (m - 1) = true) {T L P : Nat} (hP : 0 < P)
    (hper : ∀ t, T ≤ t → t + P ≤ T + L → zorb x (t + P) 0 = zorb x t 0) :
    L + 2 ≤ T + m + 2 * P := by
  -- suppose not; use column k = m + T + P - 1 + 1
  refine Nat.le_of_not_lt fun hL => ?_
  let a : Nat → Bool := fun t => zorb x t 0
  have hcols : ∀ k t, zorb x t k = cols a (k + 1) t := history_eq_cols (a := a) (fun _ => rfl)
  -- the edge time for column index i = m - 1 + t₁ is t₁
  let t₁ := T + P
  have hedge' : zorb x t₁ (m - 1 + t₁) = true :=
    zorb_edge (m := m - 1) (fun i hi => hfin i (by omega)) hedge t₁
  have hwhite : zorb x T (m - 1 + t₁) = false :=
    zorb_fin hfin T _ (by omega)
  -- periodicity of the column of index m - 1 + t₁ between T and t₁ = T + P
  have hk := cols_shift a P (m - 1 + t₁ + 1) T
  have hloc : cols (fun s => a (s + P)) (m - 1 + t₁ + 1) T = cols a (m - 1 + t₁ + 1) T := by
    apply cols_local
    intro j hj
    exact hper (T + j) (by omega) (by omega)
  rw [hloc, ← hcols, ← hcols] at hk
  rw [show T + P = t₁ from rfl] at hk
  rw [hk] at hedge'
  rw [hedge'] at hwhite
  exact absurd hwhite (by decide)

/-- **Jen (ZBL).** Column `-1` of a nonzero finite ZBL row is never eventually periodic. -/
theorem col_not_eventually_periodic {x : Nat → Bool} {m : Nat} (hm0 : 0 < m)
    (hfin : ∀ i, m ≤ i → x i = false) (hedge : x (m - 1) = true) :
    ¬ ∃ T P, 0 < P ∧ ∀ t, T ≤ t → zorb x (t + P) 0 = zorb x t 0 := by
  rintro ⟨T, P, hP, h⟩
  have := jen_clock hm0 hfin hedge (T := T) (L := T + m + 2 * P) hP (fun t ht _ => h t ht)
  omega

/-- under Q_01's constraint, a `p`-periodic stretch of the free bits `f` starting at `s₀` has length
at most `s₀ + m/2 + 2p` (in units of two steps) -/
theorem free_bits_clock {x : Nat → Bool} {m : Nat} (hm0 : 0 < m) (hfin : ∀ i, m ≤ i → x i = false)
    (hedge : x (m - 1) = true) (hc : ∀ s, zorb x (2 * s) 0 = true) {s₀ ℓ p : Nat} (hp : 0 < p)
    (hper : ∀ s, s₀ ≤ s → s + p ≤ s₀ + ℓ → zorb x (2 * (s + p) + 1) 0 = zorb x (2 * s + 1) 0) :
    2 * ℓ + 2 ≤ 2 * s₀ + m + 4 * p := by
  have := jen_clock hm0 hfin hedge (T := 2 * s₀) (L := 2 * ℓ) (P := 2 * p) (by omega) (fun t ht htL => by
    by_cases hev : t % 2 = 0
    · rw [show t = 2 * (t / 2) by omega, show 2 * (t / 2) + 2 * p = 2 * (t / 2 + p) by omega, hc, hc]
    · have := hper (t / 2) (by omega) (by omega)
      rw [show t = 2 * (t / 2) + 1 by omega, show 2 * (t / 2) + 1 + 2 * p = 2 * (t / 2 + p) + 1 by omega]
      exact this)
  omega

/-! ## Bridge: Q_01 excludes an eventually 2-periodic center column -/

open Ruliology.CellularAutomata.Rule30Prize

theorem cell_congr_int {t : Nat} {p q : Int} (h : p = q) : cell t p = cell t q := h ▸ rfl

/-- effective boundary: `cell(t,-1) || c(t) = cell(t,-1) || (c(t) && c(t+1))` -/
theorem effective_boundary (t : Nat) :
    (cell t (-1) || center t) = (cell t (-1) || (center t && center (t + 1))) := by
  have hl := cell_left t 0
  rw [show (0 : Int) - 1 = -1 by rfl] at hl
  unfold center
  rw [hl]
  cases cell (t + 1) 0 <;> cases cell t 0 <;> cases cell t (0 + 1) <;> rfl

/-- column `-1` is black at a black center time followed by a white one -/
theorem left_black (t : Nat) (h1 : center t = true) (h2 : center (t + 1) = false) :
    cell t (-1) = true := by
  have hl := cell_left t 0
  rw [show (0 : Int) - 1 = -1 by rfl] at hl
  unfold center at h1 h2
  rw [hl, h1, h2]
  rfl

/-- the left half of rule 30 at time `T`, as a ZBL row -/
def leftRow (T : Nat) (i : Nat) : Bool := cell T (-((i + 1 : Nat) : Int))

/-- while `c(t) && c(t+1)` is white, the left half of rule 30 evolves as the ZBL -/
theorem left_half_is_zbl (T : Nat) (hw : ∀ t, T ≤ t → (center t && center (t + 1)) = false) :
    ∀ t i, zorb (leftRow T) t i = cell (T + t) (-((i + 1 : Nat) : Int)) := by
  intro t
  induction t with
  | zero => intro i; rfl
  | succ t ih =>
    intro i
    rw [zorb_succ]
    cases i with
    | zero =>
      rw [zstep_zero, ih 1, ih 0]
      have hb := effective_boundary (T + t)
      rw [hw (T + t) (by omega), Bool.or_false] at hb
      show xor (cell (T + t) (-((1 + 1 : Nat) : Int))) (cell (T + t) (-((0 + 1 : Nat) : Int))) =
        cell (T + t + 1) (-((0 + 1 : Nat) : Int))
      rw [show (T + t + 1) = (T + t) + 1 by omega]
      show _ = xor (cell (T + t) (-((0 + 1 : Nat) : Int) - 1))
        (cell (T + t) (-((0 + 1 : Nat) : Int)) || cell (T + t) (-((0 + 1 : Nat) : Int) + 1))
      rw [cell_congr_int (show -((0 + 1 : Nat) : Int) - 1 = -((1 + 1 : Nat) : Int) by omega),
        cell_congr_int (show -((0 + 1 : Nat) : Int) + 1 = 0 by omega),
        cell_congr_int (show -((0 + 1 : Nat) : Int) = -1 by omega)]
      unfold center at hb
      rw [hb]
    | succ j =>
      rw [zstep_succ, ih (j + 2), ih (j + 1), ih j]
      rw [show (T + (t + 1)) = (T + t) + 1 by omega]
      show _ = xor (cell (T + t) (-((j + 1 + 1 : Nat) : Int) - 1))
        (cell (T + t) (-((j + 1 + 1 : Nat) : Int)) || cell (T + t) (-((j + 1 + 1 : Nat) : Int) + 1))
      rw [cell_congr_int (show -((j + 1 + 1 : Nat) : Int) - 1 = -((j + 2 + 1 : Nat) : Int) by omega),
        cell_congr_int (show -((j + 1 + 1 : Nat) : Int) + 1 = -((j + 1 : Nat) : Int) by omega),
        cell_congr_int (show -((j + 1 + 1 : Nat) : Int) = -((j + 1 + 1 : Nat) : Int) by omega)]

theorem leftRow_fin (T : Nat) : Fin0 (leftRow T) :=
  ⟨T, fun i hi => cell_eq_false_of_lt T _ (by omega)⟩

/-- **Q_01 excludes period 2.**  If Q_01 holds then the center column of rule 30 is not eventually
2-periodic (for any transient). -/
theorem no_eventual_period_two (hQ : Q01) : ¬ ∃ T, ∀ t, T ≤ t → center (t + 2) = center t := by
  rintro ⟨T, hT⟩
  have hper : ∀ n, center (T + 2 * n) = center T ∧ center (T + 2 * n + 1) = center (T + 1) := by
    intro n
    induction n with
    | zero => exact ⟨rfl, rfl⟩
    | succ n ih =>
      refine ⟨?_, ?_⟩
      · rw [show T + 2 * (n + 1) = (T + 2 * n) + 2 by omega, hT _ (by omega), ih.1]
      · rw [show T + 2 * (n + 1) + 1 = (T + 2 * n + 1) + 2 by omega, hT _ (by omega), ih.2]
  have hall : ∀ t, T ≤ t → center t = (if (t - T) % 2 = 0 then center T else center (T + 1)) := by
    intro t ht
    by_cases hp : (t - T) % 2 = 0
    · rw [if_pos hp, show t = T + 2 * ((t - T) / 2) by omega, (hper _).1]
    · rw [if_neg hp, show t = T + 2 * ((t - T) / 2) + 1 by omega, (hper _).2]
  by_cases heq : center T = center (T + 1)
  · apply center_not_eventually_constant
    refine ⟨T, center T, fun t ht => ?_⟩
    rw [hall t ht]
    split <;> simp [heq]
  · -- alternating from T; start at the first black time
    have bne : ∀ {b c : Bool}, ¬ b = c → c = !b := by
      intro b c h; revert h; cases b <;> cases c <;> decide
    have hc1 : center (T + 1) = !center T := bne heq
    have hwhite : ∀ t, T ≤ t → (center t && center (t + 1)) = false := by
      intro t ht
      rw [hall t ht, hall (t + 1) (by omega), hc1]
      by_cases hp : (t - T) % 2 = 0
      · rw [if_pos hp, if_neg (by omega)]
        cases center T <;> rfl
      · rw [if_neg hp, if_pos (by omega)]
        cases center T <;> rfl
    obtain ⟨T', hT'T, hblack⟩ : ∃ T', T ≤ T' ∧ ∀ s, center (T' + 2 * s) = true ∧
        center (T' + 2 * s + 1) = false := by
      cases hc : center T
      · refine ⟨T + 1, by omega, fun s => ?_⟩
        rw [hall _ (by omega), hall (T + 1 + 2 * s + 1) (by omega)]
        rw [if_neg (by omega), if_pos (by omega), hc1, hc]
        exact ⟨rfl, rfl⟩
      · refine ⟨T, Nat.le_refl T, fun s => ?_⟩
        rw [hall _ (by omega), hall (T + 2 * s + 1) (by omega)]
        rw [if_pos (by omega), if_neg (by omega), hc1, hc]
        exact ⟨rfl, rfl⟩
    refine hQ (leftRow T') (leftRow_fin T') fun s => ?_
    rw [left_half_is_zbl T' (fun t ht => hwhite t (by omega)) (2 * s) 0]
    exact left_black _ (hblack s).1 (hblack s).2


/-! ## Interface with the right half: the free bits must keep breaking periodicity -/

/-- **Jen with a clock under an alternating center.**  If the center column alternates from `T`
(black at `T + 2k`, white at `T + 2k + 1`), the column `-1` at the white times (equivalently,
by `!`, column `1` at those times) cannot be `p`-periodic on a window `[k₀, k₀ + ℓ]` (in units
of two steps) with `2ℓ + 2 > 2k₀ + T + 4p`.  In particular it is not eventually periodic. -/
theorem alternating_free_bits_clock {T : Nat}
    (hT : ∀ k, center (T + 2 * k) = true ∧ center (T + 2 * k + 1) = false)
    {k₀ ℓ p : Nat} (hp : 0 < p)
    (hper : ∀ k, k₀ ≤ k → k + p ≤ k₀ + ℓ →
      cell (T + 2 * (k + p) + 1) (-1) = cell (T + 2 * k + 1) (-1)) :
    2 * ℓ + 2 ≤ 2 * k₀ + (T + 1) + 4 * p := by
  have hw : ∀ t, T ≤ t → (center t && center (t + 1)) = false := by
    intro t ht
    obtain ⟨j, rfl | rfl⟩ : ∃ j, t = T + 2 * j ∨ t = T + 2 * j + 1 := ⟨(t - T) / 2, by omega⟩
    · rw [(hT j).2]; cases center (T + 2 * j) <;> rfl
    · rw [show T + 2 * j + 1 + 1 = T + 2 * (j + 1) by omega, (hT j).2]; rfl
  have hz := left_half_is_zbl T hw
  -- work with the row at time `T + 1`, whose leftmost black cell is at `-(T + 1)` (index `T`)
  have hedge1 : zorb (leftRow T) 1 T = true := by
    rw [hz 1 T, show -((T + 1 : Nat) : Int) = -((T + 1 : Nat) : Int) from rfl]
    exact cell_left_edge (T + 1)
  have hfin1 : ∀ i, T + 1 ≤ i → zorb (leftRow T) 1 i = false := by
    intro i hi
    rw [hz 1 i]; exact cell_eq_false_of_lt (T + 1) _ (by omega)
  -- apply `jen_clock` to the row at time `T + 1` with edge index `T` (m = T + 1); its column `-1`
  -- at time `t` is `cell (T + 1 + t) (-1)`
  have hcol : ∀ t, zorb (zorb (leftRow T) 1) t 0 = cell (T + 1 + t) (-1) := by
    intro t; rw [zorb_add, hz (1 + t) 0, show T + (1 + t) = T + 1 + t by omega]; rfl
  have := jen_clock (x := zorb (leftRow T) 1) (m := T + 1) (by omega) hfin1
    (by simpa using hedge1) (T := 2 * k₀) (L := 2 * ℓ) (P := 2 * p) (by omega) (fun t ht htL => by
      rw [hcol, hcol]
      by_cases hev : t % 2 = 0
      · -- times T + 1 + t with t even are the white times T + 2k + 1
        have := hper (t / 2) (by omega) (by omega)
        rw [show T + 1 + (t + 2 * p) = T + 2 * (t / 2 + p) + 1 by omega,
          show T + 1 + t = T + 2 * (t / 2) + 1 by omega]
        exact this
      · -- black times: column -1 is black there
        rw [show T + 1 + (t + 2 * p) = T + 2 * (t / 2 + p + 1) by omega,
          show T + 1 + t = T + 2 * (t / 2 + 1) by omega]
        have hb : ∀ k, cell (T + 2 * k) (-1) = true := fun k =>
          left_black _ (hT k).1 (by rw [show T + 2 * k + 1 = T + 2 * k + 1 from rfl]; exact (hT k).2)
        rw [hb, hb])
  omega

/-- at a white center time followed by a black one, columns `-1` and `1` are complementary -/
theorem left_right_white (t : Nat) (h1 : center t = false) (h2 : center (t + 1) = true) :
    cell t 1 = !cell t (-1) := by
  have hl := cell_left t 0
  rw [show (0 : Int) - 1 = -1 by rfl] at hl
  unfold center at h1 h2
  rw [hl, h1, h2, show (0 : Int) + 1 = 1 by rfl]
  cases cell t 1 <;> rfl

/-- **Interface for the right half (Program B).**  If the center alternates from `T`, column `1`
of rule 30 at the white times `T + 2k + 1` is not `p`-periodic on any window `[k₀, k₀ + ℓ]` with
`2ℓ + 2 > 2k₀ + T + 4p`.  So a proof that the right half driven by `0101…` produces such a long
periodic window (for instance, that its column `1` is eventually periodic at the white times)
would exclude period 2. -/
theorem alternating_right_col1_clock {T : Nat}
    (hT : ∀ k, center (T + 2 * k) = true ∧ center (T + 2 * k + 1) = false)
    {k₀ ℓ p : Nat} (hp : 0 < p)
    (hper : ∀ k, k₀ ≤ k → k + p ≤ k₀ + ℓ →
      cell (T + 2 * (k + p) + 1) 1 = cell (T + 2 * k + 1) 1) :
    2 * ℓ + 2 ≤ 2 * k₀ + (T + 1) + 4 * p := by
  have hw : ∀ k, cell (T + 2 * k + 1) 1 = !cell (T + 2 * k + 1) (-1) := fun k =>
    left_right_white _ (hT k).2 (by rw [show T + 2 * k + 1 + 1 = T + 2 * (k + 1) by omega]; exact (hT (k + 1)).1)
  refine alternating_free_bits_clock hT hp fun k h1 h2 => ?_
  have := hper k h1 h2
  rw [hw, hw] at this
  cases h : cell (T + 2 * (k + p) + 1) (-1) <;> cases h' : cell (T + 2 * k + 1) (-1) <;> simp_all

/-! ## Equivalence with the staged `Rule30PeriodTwo.Q01` -/

open Ruliology.CellularAutomata

theorem L_eq_zorb (s : Int → Bool) : ∀ t i,
    Rule30DrivenLeft.L (fun _ => false) s t (-((i + 1 : Nat) : Int)) =
      zorb (fun i => s (-((i + 1 : Nat) : Int))) t i := by
  intro t
  induction t with
  | zero => intro i; exact Rule30DrivenLeft.L_zero (by omega)
  | succ t ih =>
    intro i
    rw [Rule30DrivenLeft.L_succ (by omega), zorb_succ]
    cases i with
    | zero =>
      rw [zstep_zero, ← ih 1, ← ih 0,
        cell_congr_L (show -((0 + 1 : Nat) : Int) - 1 = -((1 + 1 : Nat) : Int) by omega),
        cell_congr_L (show -((0 + 1 : Nat) : Int) + 1 = 0 by omega), Rule30DrivenLeft.L_col0]
      show xor _ (_ || false) = _
      cases Rule30DrivenLeft.L (fun _ => false) s t (-((1 + 1 : Nat) : Int)) <;>
        cases Rule30DrivenLeft.L (fun _ => false) s t (-((0 + 1 : Nat) : Int)) <;> rfl
    | succ j =>
      rw [zstep_succ, ← ih (j + 2), ← ih (j + 1), ← ih j,
        cell_congr_L (show -((j + 1 + 1 : Nat) : Int) - 1 = -((j + 2 + 1 : Nat) : Int) by omega),
        cell_congr_L (show -((j + 1 + 1 : Nat) : Int) + 1 = -((j + 1 : Nat) : Int) by omega)]
      rfl
where
  cell_congr_L {t : Nat} {p q : Int} (h : p = q) :
      Rule30DrivenLeft.L (fun _ => false) s t p = Rule30DrivenLeft.L (fun _ => false) s t q := h ▸ rfl

/-- a finite row that is black next to the wall has a leftmost black cell -/
theorem leftmost {x : Nat → Bool} (h0 : x 0 = true) : ∀ M, (∀ i, M ≤ i → x i = false) →
    ∃ m, 0 < m ∧ x (m - 1) = true ∧ ∀ i, m ≤ i → x i = false := by
  intro M
  induction M with
  | zero => intro h; rw [h 0 (by omega)] at h0; exact absurd h0 (by decide)
  | succ M ih =>
    intro h
    by_cases hM : x M = true
    · exact ⟨M + 1, by omega, hM, h⟩
    · exact ih fun i hi => by
        by_cases hiM : i = M
        · subst hiM; cases hx : x i <;> simp_all
        · exact h i (by omega)

/-- **My `Q01` is the staged `Rule30PeriodTwo.Q01`.** -/
theorem Q01_iff_staged : Q01 ↔ Rule30PeriodTwo.Q01 := by
  constructor
  · intro hQ m s hm hs0 _ hc
    refine hQ (fun i => s (-((i + 1 : Nat) : Int))) ⟨m, fun i hi => hs0 _ (by omega)⟩ fun k => ?_
    rw [← L_eq_zorb s (2 * k) 0]
    exact hc k
  · intro hS x ⟨M, hM⟩ hc
    have h0 : x 0 = true := hc 0
    obtain ⟨m, hm, hedge, hfin⟩ := leftmost h0 M hM
    let s : Int → Bool := fun p => if p < 0 then x (-p - 1).toNat else false
    have hsx : (fun i => s (-((i + 1 : Nat) : Int))) = x := by
      funext i
      simp only [s]
      rw [if_pos (by omega), show (-(-((i + 1 : Nat) : Int)) - 1).toNat = i by omega]
    refine hS m s hm (fun p hp => ?_) ?_ fun k => ?_
    · simp only [s]; rw [if_pos (by omega)]; exact hfin _ (by omega)
    · simp only [s]; rw [if_pos (by omega), show (-(-(m : Int)) - 1).toNat = m - 1 by omega]
      exact hedge
    · rw [show (-1 : Int) = -((0 + 1 : Nat) : Int) by rfl, L_eq_zorb s (2 * k) 0, hsx]
      exact hc k

end R30ProgA

#print axioms R30ProgA.two_step_shift

#print axioms R30ProgA.back_fin_iff

#print axioms R30ProgA.edge_region_barrier

#print axioms R30ProgA.survive_iff

#print axioms R30ProgA.no_two_white

#print axioms R30ProgA.jen_clock

#print axioms R30ProgA.free_bits_clock

#print axioms R30ProgA.alternating_right_col1_clock

#print axioms R30ProgA.Q01_iff_bounded

#print axioms R30ProgA.Q01_iff_staged

#print axioms R30ProgA.no_eventual_period_two
