import Ruliology.CellularAutomata.Rule30PeriodTwo

namespace Ruliology.CellularAutomata
namespace Rule30ZeroBoundary

open Rule30Jen Rule30Prize

/-! ### The dynamics -/

/-- The zero-boundary left half (ZBL): rule 30 on the positions `-1, -2, …` with position `0`
held white. `zrow L t k` is the color at time `t` of the cell at depth `k` (position `-k`); depth
`0` is the wall. The start `L` is read at depths `k ≥ 1` (`L 0` is ignored). -/
def zrow (L : Nat → Bool) : Nat → Nat → Bool
  | 0, k => if k = 0 then false else L k
  | t + 1, k => if k = 0 then false else xor (zrow L t (k + 1)) (zrow L t k || zrow L t (k - 1))

theorem zrow_wall (L : Nat → Bool) : ∀ t, zrow L t 0 = false
  | 0 => rfl
  | _ + 1 => rfl

theorem zrow_zero (L : Nat → Bool) (k : Nat) : zrow L 0 (k + 1) = L (k + 1) := rfl

theorem zrow_zero_of_pos (L : Nat → Bool) {k : Nat} (hk : 1 ≤ k) : zrow L 0 k = L k := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rfl

theorem zrow_succ (L : Nat → Bool) (t k : Nat) :
    zrow L (t + 1) (k + 1) = xor (zrow L t (k + 2)) (zrow L t (k + 1) || zrow L t k) := rfl

/-- Left-permutive inversion inside the ZBL. -/
theorem zrow_inv (L : Nat → Bool) (t k : Nat) :
    zrow L t (k + 2) = xor (zrow L (t + 1) (k + 1)) (zrow L t (k + 1) || zrow L t k) := by
  rw [zrow_succ]; cases zrow L t (k + 2) <;> cases (zrow L t (k + 1) || zrow L t k) <;> rfl

/-- The ZBL is a semiflow: the row at time `s` restarts the run. -/
theorem zrow_shift (L : Nat → Bool) (s : Nat) : ∀ t k, zrow L (s + t) k = zrow (zrow L s) t k := by
  intro t
  induction t with
  | zero =>
    intro k
    cases k with
    | zero => simp [zrow_wall]
    | succ k => rfl
  | succ t ih =>
    intro k
    cases k with
    | zero => simp [zrow_wall]
    | succ k =>
      rw [show s + (t + 1) = (s + t) + 1 by omega, zrow_succ, zrow_succ, ih, ih, ih]

/-- The row at time `0` is the start with a white wall. -/
theorem zrow_zero_self {L : Nat → Bool} (h : L 0 = false) : zrow L 0 = L := by
  funext k
  cases k with
  | zero => exact h.symm
  | succ k => rfl

/-- The run only sees the start at depths `≥ 1`. -/
theorem zrow_congr {L L' : Nat → Bool} (h : ∀ k, 1 ≤ k → L k = L' k) : ∀ t k, zrow L t k = zrow L' t k := by
  intro t
  induction t with
  | zero =>
    intro k
    cases k with
    | zero => rfl
    | succ k => exact h (k + 1) (by omega)
  | succ t ih =>
    intro k
    cases k with
    | zero => rfl
    | succ k => rw [zrow_succ, zrow_succ, ih, ih, ih]

/-! ### The stripe -/

/-- The stripe `…10101`: black exactly at the odd depths. -/
def stripe (k : Nat) : Bool := k % 2 == 1

theorem stripe_succ (k : Nat) : stripe (k + 1) = !stripe k := by
  unfold stripe
  rcases Nat.mod_two_eq_zero_or_one k with h | h
  · have : (k + 1) % 2 = 1 := by omega
    simp [h, this]
  · have : (k + 1) % 2 = 0 := by omega
    simp [h, this]

theorem stripe_add_two (k : Nat) : stripe (k + 2) = stripe k := by
  rw [stripe_succ, stripe_succ]; simp

theorem stripe_or (k : Nat) : (stripe (k + 1) || stripe k) = true := by
  rw [stripe_succ]; cases stripe k <;> rfl

theorem stripe_odd {k : Nat} (h : k % 2 = 1) : stripe k = true := by unfold stripe; simp [h]
theorem stripe_even {k : Nat} (h : k % 2 = 0) : stripe k = false := by unfold stripe; simp [h]

/-- The local rule fixes the stripe. -/
theorem stripe_step (k : Nat) : stripe (k + 1) = xor (stripe (k + 2)) (stripe (k + 1) || stripe k) := by
  rw [stripe_or, stripe_add_two, stripe_succ]; cases stripe k <;> rfl

/-- The stripe is a fixed point of the ZBL. -/
theorem zrow_stripe : ∀ t k, zrow stripe t k = stripe k := by
  intro t
  induction t with
  | zero =>
    intro k
    cases k with
    | zero => rfl
    | succ k => rfl
  | succ t ih =>
    intro k
    cases k with
    | zero => rfl
    | succ k => rw [zrow_succ, ih, ih, ih, ← stripe_step]

/-! ### Finite rows -/

/-- A row is finitely supported: white beyond some depth. -/
def FinSupp (L : Nat → Bool) : Prop := ∃ W, ∀ k, W < k → L k = false

/-- The support grows by at most one depth per step. -/
theorem zrow_fin {L : Nat → Bool} {W : Nat} (h : ∀ k, W < k → L k = false) :
    ∀ t k, W + t < k → zrow L t k = false := by
  intro t
  induction t with
  | zero =>
    intro k hk
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    exact h _ (by omega)
  | succ t ih =>
    intro k hk
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [zrow_succ, ih _ (by omega), ih _ (by omega), ih _ (by omega)]
    rfl

/-- **The edge moves out by one depth per step.** If the last black cell of the start is at depth
`m ≥ 1`, the last black cell at time `t` is at depth `m + t`. -/
theorem zrow_edge {L : Nat → Bool} {m : Nat} (hm : 1 ≤ m) (hedge : L m = true)
    (hfin : ∀ k, m < k → L k = false) :
    ∀ t, zrow L t (m + t) = true ∧ ∀ k, m + t < k → zrow L t k = false := by
  intro t
  induction t with
  | zero =>
    refine ⟨?_, fun k hk => ?_⟩
    · rw [Nat.add_zero, zrow_zero_of_pos L hm, hedge]
    · rw [zrow_zero_of_pos L (by omega), hfin k (by omega)]
  | succ t ih =>
    refine ⟨?_, fun k hk => ?_⟩
    · rw [show m + (t + 1) = (m + t) + 1 by omega, zrow_succ, ih.2 (m + t + 2) (by omega),
        ih.2 (m + t + 1) (by omega), ih.1]
      rfl
    · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      rw [zrow_succ, ih.2 _ (by omega), ih.2 _ (by omega), ih.2 _ (by omega)]
      rfl

/-- A finitely supported row that is black at depth `1` has a last black cell. -/
theorem last_black {L : Nat → Bool} (h1 : L 1 = true) :
    ∀ W, (∀ k, W < k → L k = false) → ∃ m, 1 ≤ m ∧ L m = true ∧ ∀ k, m < k → L k = false := by
  intro W
  induction W with
  | zero => intro hz; exact absurd (hz 1 (by omega)) (by rw [h1]; decide)
  | succ W ih =>
    intro hz
    cases hW : L (W + 1)
    · exact ih fun k hk => by
        rcases Nat.lt_or_ge (W + 1) k with h | h
        · exact hz k h
        · rw [show k = W + 1 by omega]; exact hW
    · exact ⟨W + 1, by omega, hW, fun k hk => hz k hk⟩

/-! ### Locality -/

/-- **Light cone.** The cell at depth `k` and time `t` only depends on the start at depths
`1, …, k + t`. -/
theorem zrow_light_cone {L L' : Nat → Bool} :
    ∀ t k, (∀ i, 1 ≤ i → i ≤ k + t → L i = L' i) → zrow L t k = zrow L' t k := by
  intro t
  induction t with
  | zero =>
    intro k h
    cases k with
    | zero => rfl
    | succ k => exact h (k + 1) (by omega) (by omega)
  | succ t ih =>
    intro k h
    cases k with
    | zero => rfl
    | succ j =>
      rw [zrow_succ, zrow_succ, ih (j + 2) (fun i h1 h2 => h i h1 (by omega)),
        ih (j + 1) (fun i h1 h2 => h i h1 (by omega)), ih j (fun i h1 h2 => h i h1 (by omega))]

/-- **Outer locality.** Starts that agree from depth `a ≥ 1` on agree at time `s` from depth
`a + s` on. -/
theorem zrow_local {L L' : Nat → Bool} {a : Nat} (ha : 1 ≤ a) (h : ∀ k, a ≤ k → L k = L' k) :
    ∀ s k, a + s ≤ k → zrow L s k = zrow L' s k := by
  intro s
  induction s with
  | zero =>
    intro k hk
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    exact h _ (by omega)
  | succ s ih =>
    intro k hk
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [zrow_succ, zrow_succ, ih (k' + 2) (by omega), ih (k' + 1) (by omega), ih k' (by omega)]

/-- **Translation away from the wall.** If `L'` is `L` moved out by `d` depths from depth `a ≥ 1`
on, the runs agree (moved out by `d`) at time `t` from depth `a + t` on. -/
theorem zrow_translate {L L' : Nat → Bool} {d a : Nat} (ha : 1 ≤ a)
    (h : ∀ k, a ≤ k → L' (k + d) = L k) : ∀ t k, a + t ≤ k → zrow L' t (k + d) = zrow L t k := by
  intro t
  induction t with
  | zero =>
    intro k hk
    rw [zrow_zero_of_pos L' (by omega), zrow_zero_of_pos L (by omega), h k (by omega)]
  | succ t ih =>
    intro k hk
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [show j + 1 + d = (j + d) + 1 by omega, zrow_succ, zrow_succ,
      show j + d + 2 = (j + 2) + d by omega, show j + d + 1 = (j + 1) + d by omega,
      ih (j + 2) (by omega), ih (j + 1) (by omega), show j + d = j + d from rfl]
    obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    rw [show i + 1 + d = (i + 1) + d from rfl, ih (i + 1) (by omega)]

/-- **Pivot, general depth.** If two starts agree at depths `1, …, k + t - 1`, the cells at depth
`k ≥ 1` and time `t` differ exactly when the starts differ at depth `k + t`. -/
theorem zrow_aff : ∀ t (L L' : Nat → Bool) (k : Nat), 1 ≤ k →
    (∀ i, 1 ≤ i → i < k + t → L i = L' i) →
    xor (zrow L t k) (zrow L' t k) = xor (L (k + t)) (L' (k + t)) := by
  intro t
  induction t with
  | zero => intro L L' k hk _; rw [zrow_zero_of_pos L hk, zrow_zero_of_pos L' hk]; rfl
  | succ t ih =>
    intro L L' k hk h
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [zrow_succ, zrow_succ,
      zrow_light_cone t (j + 1) (fun i h1 h2 => h i h1 (by omega)),
      zrow_light_cone t j (fun i h1 h2 => h i h1 (by omega))]
    have key := ih L L' (j + 2) (by omega) (fun i h1 h2 => h i h1 (by omega))
    rw [show j + 1 + (t + 1) = j + 2 + t by omega, ← key]
    generalize zrow L t (j + 2) = a
    generalize zrow L' t (j + 2) = b
    generalize (zrow L' t (j + 1) || zrow L' t j) = c
    cases a <;> cases b <;> cases c <;> rfl

/-- **Pivot.** Two starts that agree at depths `1, …, t` and differ at depth `t + 1` have different
cells at depth `1` at time `t`. -/
theorem pivot {L L' : Nat → Bool} {t : Nat} (hagree : ∀ i, 1 ≤ i → i ≤ t → L i = L' i)
    (hdiff : L (t + 1) ≠ L' (t + 1)) : zrow L t 1 ≠ zrow L' t 1 := by
  have key := zrow_aff t L L' 1 (Nat.le_refl 1) (fun i h1 h2 => hagree i h1 (by omega))
  rw [show 1 + t = t + 1 by omega] at key
  intro he
  apply hdiff
  rw [he] at key
  revert key
  cases zrow L' t 1 <;> cases L (t + 1) <;> cases L' (t + 1) <;> decide

/-- The start cut off below depth `d`: `L` at depths `≤ d`, white beyond. -/
def truncate (L : Nat → Bool) (d : Nat) (k : Nat) : Bool := L k && decide (k ≤ d)

theorem truncate_fin (L : Nat → Bool) (d : Nat) : ∀ k, d < k → truncate L d k = false := by
  intro k hk; simp [truncate]; omega

/-- **Zero-run localization.** If the start is white at depths `d + 1, …, d + n`, column `-1`
agrees with that of the truncation at depth `d` up to time `d + n - 1`. -/
theorem zero_run_local {L : Nat → Bool} {d n : Nat} (hz : ∀ k, d < k → k ≤ d + n → L k = false) :
    ∀ t, t < d + n → zrow L t 1 = zrow (truncate L d) t 1 := by
  intro t ht
  apply zrow_light_cone
  intro i _ hi
  unfold truncate
  by_cases hid : i ≤ d
  · simp [hid]
  · simp [hid, hz i (by omega) (by omega)]

/-- **Near-wall completion.** Any far part `z` (depths `> d`) can be completed at depths `1, …, d`
so that column `-1` follows any prescribed values `c` up to time `d - 1`. -/
theorem complete_near_wall (z c : Nat → Bool) :
    ∀ d, ∃ L : Nat → Bool, (∀ k, d < k → L k = z k) ∧ ∀ t, t < d → zrow L t 1 = c t := by
  intro d
  induction d with
  | zero => exact ⟨z, fun _ _ => rfl, fun t ht => absurd ht (by omega)⟩
  | succ d ih =>
    obtain ⟨L, hLz, hLc⟩ := ih
    by_cases hok : zrow L d 1 = c d
    · exact ⟨L, fun k hk => hLz k (by omega), fun t ht => by
        by_cases htd : t = d
        · subst htd; exact hok
        · exact hLc t (by omega)⟩
    · let L' : Nat → Bool := fun k => if k = d + 1 then !L (d + 1) else L k
      have hagree : ∀ i, 1 ≤ i → i ≤ d → L' i = L i := fun i _ hi => by
        simp [L', show i ≠ d + 1 by omega]
      have hdiff : L' (d + 1) ≠ L (d + 1) := by simp [L']
      have hflip := pivot hagree hdiff
      refine ⟨L', fun k hk => ?_, fun t ht => ?_⟩
      · simp only [L', show k ≠ d + 1 by omega, if_false]; exact hLz k (by omega)
      · by_cases htd : t = d
        · subst htd
          revert hflip hok
          cases zrow L' t 1 <;> cases zrow L t 1 <;> cases c t <;> simp
        · rw [zrow_light_cone t 1 (fun i h1 h2 => hagree i h1 (by omega))]
          exact hLc t (by omega)

/-- **Edge-region barrier.** Fix any far part `z` and any prescribed column `c`. For every `d` there
is a start that agrees with `z` beyond depth `d` (so its run agrees with that of `z` beyond depth
`d + t` at time `t`, including every left diagonal of the edge region) and whose column `-1`
follows `c` up to time `d - 1`. -/
theorem edge_region_barrier (z c : Nat → Bool) (d : Nat) :
    ∃ L : Nat → Bool, (∀ k, d < k → L k = z k) ∧ (∀ t, t < d → zrow L t 1 = c t) ∧
      ∀ t k, d + 1 + t ≤ k → zrow L t k = zrow z t k := by
  obtain ⟨L, hLz, hLc⟩ := complete_near_wall z c d
  exact ⟨L, hLz, hLc, zrow_local (a := d + 1) (by omega) (fun k hk => hLz k (by omega))⟩

/-! ### Backward determinism -/

/-- **Backward determinism.** Two rows with the same image and the same cell at depth `1` agree.
In a constrained history the depth-`1` cell is forced (black) at every other step. -/
theorem backward_det {L L' : Nat → Bool} {t : Nat} (h : ∀ k, zrow L (t + 1) k = zrow L' (t + 1) k)
    (h1 : zrow L t 1 = zrow L' t 1) : ∀ k, zrow L t k = zrow L' t k := by
  have key : ∀ n, zrow L t n = zrow L' t n ∧ zrow L t (n + 1) = zrow L' t (n + 1) := by
    intro n
    induction n with
    | zero => exact ⟨by rw [zrow_wall, zrow_wall], h1⟩
    | succ n ih =>
      refine ⟨ih.2, ?_⟩
      rw [zrow_inv L t n, zrow_inv L' t n, h (n + 1), ih.1, ih.2]
  exact fun k => (key k).1

/-- **A history is determined by its last row and its column `-1`.** -/
theorem history_det {L L' : Nat → Bool} {T : Nat} (hT : ∀ k, zrow L T k = zrow L' T k)
    (h1 : ∀ t, t < T → zrow L t 1 = zrow L' t 1) : ∀ t, t ≤ T → ∀ k, zrow L t k = zrow L' t k := by
  have key : ∀ n, n ≤ T → ∀ k, zrow L (T - n) k = zrow L' (T - n) k := by
    intro n
    induction n with
    | zero => intro _; simpa using hT
    | succ n ih =>
      intro hn
      apply backward_det
      · rw [show T - (n + 1) + 1 = T - n by omega]
        exact ih (by omega)
      · exact h1 _ (by omega)
  intro t ht
  have := key (T - t) (by omega)
  rwa [show T - (T - t) = t by omega] at this

/-- The backward transducer: the unique preimage of the row `y` with depth-`1` cell `b`. -/
def back (b : Bool) (y : Nat → Bool) : Nat → Bool
  | 0 => false
  | 1 => b
  | k + 2 => xor (y (k + 1)) (back b y (k + 1) || back b y k)

theorem zrow_back_zero (b : Bool) (y : Nat → Bool) : zrow (back b y) 0 = back b y :=
  zrow_zero_self rfl

/-- `back b y` is a preimage of `y`. -/
theorem zrow_back (b : Bool) (y : Nat → Bool) : ∀ k, 1 ≤ k → zrow (back b y) 1 k = y k := by
  intro k hk
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [zrow_succ, zrow_back_zero]
  show xor (xor (y (j + 1)) (back b y (j + 1) || back b y j)) (back b y (j + 1) || back b y j) = y (j + 1)
  cases y (j + 1) <;> cases (back b y (j + 1) || back b y j) <;> rfl

/-- Every preimage is given by the backward transducer. -/
theorem eq_back {L y : Nat → Bool} (h : ∀ k, 1 ≤ k → zrow L 1 k = y k) :
    ∀ k, zrow L 0 k = back (L 1) y k := by
  have hstep : ∀ k, zrow L 1 k = zrow (back (L 1) y) 1 k := by
    intro k
    cases k with
    | zero => rw [zrow_wall, zrow_wall]
    | succ k => rw [h (k + 1) (by omega), zrow_back _ _ (k + 1) (by omega)]
  have := backward_det (t := 0) hstep rfl
  intro k
  rw [this k, zrow_back_zero]

/-- **Finite-preimage criterion.** If `y` is white from depth `n ≥ 2` on, its preimage with
depth-`1` cell `b` is finitely supported iff the backward transducer is white at depths `n - 1`
and `n`. -/
theorem back_fin_iff (b : Bool) {y : Nat → Bool} {n : Nat} (hn : 2 ≤ n)
    (hy : ∀ k, n ≤ k → y k = false) :
    FinSupp (back b y) ↔ (back b y (n - 1) = false ∧ back b y n = false) := by
  constructor
  · rintro ⟨M, hM⟩
    have prop : ∀ j, (back b y (n - 1 + j) || back b y (n + j)) = true →
        back b y (n + j + 1) = true := by
      intro j hj
      rw [show n + j + 1 = (n + j - 1) + 2 by omega, back, hy _ (by omega),
        show n + j - 1 + 1 = n + j by omega, show n + j - 1 = n - 1 + j by omega]
      rw [Bool.or_comm] at hj
      simp [hj]
    refine Classical.byContradiction fun hne => ?_
    have h0 : (back b y (n - 1 + 0) || back b y (n + 0)) = true := by
      cases h1 : back b y (n - 1) <;> cases h2 : back b y n <;> simp_all
    have allb : ∀ j, back b y (n + j + 1) = true := by
      intro j
      induction j with
      | zero => exact prop 0 h0
      | succ j ih =>
        apply prop (j + 1)
        simp [show n + (j + 1) = n + j + 1 by omega, ih]
    have := allb M
    rw [hM _ (by omega)] at this
    exact absurd this (by decide)
  · rintro ⟨h1, h2⟩
    refine ⟨n - 1, fun k hk => ?_⟩
    have all : ∀ j, back b y (n - 1 + j) = false ∧ back b y (n + j) = false := by
      intro j
      induction j with
      | zero => exact ⟨h1, h2⟩
      | succ j ih =>
        refine ⟨by rw [show n - 1 + (j + 1) = n + j by omega]; exact ih.2, ?_⟩
        rw [show n + (j + 1) = (n - 1 + j) + 2 by omega, back, hy _ (by omega),
          show n - 1 + j + 1 = n + j by omega, ih.2, ih.1]
        rfl
    have := (all (k - (n - 1))).1
    rwa [show n - 1 + (k - (n - 1)) = k by omega] at this

