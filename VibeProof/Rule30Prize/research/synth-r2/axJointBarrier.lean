import Ruliology.CellularAutomata.Rule30Jen

/-!
# Joint (two-sided) barrier for local ranking functions, period 2

Rule 30 on the full line from an arbitrary configuration (`evol`). The spatially 7-periodic configuration
`c7` (black exactly at `p ≡ 6 mod 7`) is temporally 4-periodic and its column 0 alternates `0,1,0,1,...`.
Its truncations to `[-(7N+1), 7N+6]` are finite configurations whose center column alternates for about
`7N` steps.

`no_joint_local_ranking`: there is no function `R lo hi C L E` (leftmost black position, rightmost black
position, center window, left-edge window, right-edge window) into `Nat` that strictly decreases along every
step of every finite configuration at which the center column flips. So no ranking function built from
the two widths and bounded windows at the center and at both edges can prove that the center column of
rule 30 from a finite configuration is never eventually 2-periodic.
-/

namespace JointBarrier
open Ruliology.CellularAutomata.Rule30Jen

def evol (x : Int → Bool) : Nat → Int → Bool
  | 0, p => x p
  | t + 1, p => rule (evol x t (p - 1)) (evol x t p) (evol x t (p + 1))

theorem evol_succ (x : Int → Bool) (t : Nat) (p : Int) :
    evol x (t + 1) p = rule (evol x t (p - 1)) (evol x t p) (evol x t (p + 1)) := rfl

theorem evol_restart (x : Int → Bool) (a : Nat) : ∀ b p, evol (fun p => evol x a p) b p = evol x (a + b) p := by
  intro b
  induction b with
  | zero => intro p; rfl
  | succ b ih =>
    intro p
    rw [show a + (b + 1) = (a + b) + 1 by omega, evol_succ, evol_succ, ih, ih, ih]

theorem evol_shift_all {x x' : Int → Bool} {d : Int} (h : ∀ p, x' (p + d) = x p) :
    ∀ t p, evol x' t (p + d) = evol x t p := by
  intro t
  induction t with
  | zero => intro p; exact h p
  | succ t ih =>
    intro p
    rw [evol_succ, evol_succ, show p + d - 1 = (p - 1) + d by omega, show p + d + 1 = (p + 1) + d by omega,
      ih, ih, ih]

/-- Locality with translation, region bounded above. -/
theorem evol_local_le {x x' : Int → Bool} {d b : Int} (h : ∀ p, p ≤ b → x' (p + d) = x p) :
    ∀ (t : Nat) p, p + t ≤ b → evol x' t (p + d) = evol x t p := by
  intro t
  induction t with
  | zero => intro p hp; exact h p (by omega)
  | succ t ih =>
    intro p hp
    rw [evol_succ, evol_succ, show p + d - 1 = (p - 1) + d by omega, show p + d + 1 = (p + 1) + d by omega,
      ih (p - 1) (by omega), ih p (by omega), ih (p + 1) (by omega)]

/-- Locality with translation, region bounded below. -/
theorem evol_local_ge {x x' : Int → Bool} {d a : Int} (h : ∀ p, a ≤ p → x' (p + d) = x p) :
    ∀ (t : Nat) p, a + t ≤ p → evol x' t (p + d) = evol x t p := by
  intro t
  induction t with
  | zero => intro p hp; exact h p (by omega)
  | succ t ih =>
    intro p hp
    rw [evol_succ, evol_succ, show p + d - 1 = (p - 1) + d by omega, show p + d + 1 = (p + 1) + d by omega,
      ih (p - 1) (by omega), ih p (by omega), ih (p + 1) (by omega)]

/-- Locality in a window. -/
theorem evol_local {x x' : Int → Bool} {a b : Int} (h : ∀ p, a ≤ p → p ≤ b → x' p = x p) :
    ∀ (t : Nat) p, a + t ≤ p → p + t ≤ b → evol x' t p = evol x t p := by
  intro t
  induction t with
  | zero => intro p h1 h2; exact h p (by omega) (by omega)
  | succ t ih =>
    intro p h1 h2
    rw [evol_succ, evol_succ, ih (p - 1) (by omega) (by omega), ih p (by omega) (by omega),
      ih (p + 1) (by omega) (by omega)]

/-- Left edge: the leftmost black cell moves left by one per step. -/
theorem left_edge {x : Int → Bool} {lo : Int} (h1 : x lo = true) (h0 : ∀ p, p < lo → x p = false) :
    ∀ t : Nat, evol x t (lo - t) = true ∧ ∀ p, p < lo - t → evol x t p = false := by
  intro t
  induction t with
  | zero => exact ⟨by simpa using h1, fun p hp => h0 p (by omega)⟩
  | succ t ih =>
    refine ⟨?_, fun p hp => ?_⟩
    · rw [evol_succ, ih.2 _ (by omega), ih.2 _ (by omega), show lo - ↑(t + 1) + 1 = lo - ↑t by omega, ih.1]; rfl
    · rw [evol_succ, ih.2 _ (by omega), ih.2 _ (by omega), ih.2 _ (by omega)]; rfl

/-- Right edge: the rightmost black cell moves right by one per step. -/
theorem right_edge {x : Int → Bool} {hi : Int} (h1 : x hi = true) (h0 : ∀ p, hi < p → x p = false) :
    ∀ t : Nat, evol x t (hi + t) = true ∧ ∀ p, hi + t < p → evol x t p = false := by
  intro t
  induction t with
  | zero => exact ⟨by simpa using h1, fun p hp => h0 p (by omega)⟩
  | succ t ih =>
    refine ⟨?_, fun p hp => ?_⟩
    · rw [evol_succ, show hi + ↑(t + 1) - 1 = hi + t by omega, ih.1, ih.2 _ (by omega), ih.2 _ (by omega)]; rfl
    · rw [evol_succ, ih.2 _ (by omega), ih.2 _ (by omega), ih.2 _ (by omega)]; rfl

/-! ## The 7-periodic configuration -/

def c7 (p : Int) : Bool := decide ((p + 1) % 7 = 0)

theorem c7_shift (p k : Int) : c7 (p + 7 * k) = c7 p := by
  unfold c7
  have : (p + 7 * k + 1) % 7 = (p + 1) % 7 := by omega
  rw [this]

theorem evol_c7_shift (t : Nat) (p k : Int) : evol c7 t (p + 7 * k) = evol c7 t p :=
  evol_shift_all (fun p => c7_shift p k) t p

theorem evol_c7_four (p : Int) : evol c7 4 p = c7 p := by
  have hp : p = p % 7 + 7 * (p / 7) := by omega
  rw [hp, evol_c7_shift, c7_shift]
  have hr : p % 7 = 0 ∨ p % 7 = 1 ∨ p % 7 = 2 ∨ p % 7 = 3 ∨ p % 7 = 4 ∨ p % 7 = 5 ∨ p % 7 = 6 := by omega
  rcases hr with h | h | h | h | h | h | h <;> rw [h] <;> decide

theorem evol_c7_period (t : Nat) (p : Int) : evol c7 (t + 4) p = evol c7 t p := by
  have h4 : (fun p => evol c7 4 p) = c7 := funext evol_c7_four
  rw [show t + 4 = 4 + t by omega, ← evol_restart, h4]

theorem evol_c7_period_mul (t k : Nat) (p : Int) : evol c7 (t + 4 * k) p = evol c7 t p := by
  induction k with
  | zero => rfl
  | succ k ih => rw [show t + 4 * (k + 1) = (t + 4 * k) + 4 by omega, evol_c7_period, ih]

/-- Column 0 of the 7-periodic configuration alternates. -/
theorem c7_center (t : Nat) : evol c7 (t + 1) 0 = !evol c7 t 0 := by
  have ht : t = t % 4 + 4 * (t / 4) := by omega
  rw [ht, show t % 4 + 4 * (t / 4) + 1 = (t % 4 + 1) + 4 * (t / 4) by omega, evol_c7_period_mul,
    evol_c7_period_mul]
  have hr : t % 4 = 0 ∨ t % 4 = 1 ∨ t % 4 = 2 ∨ t % 4 = 3 := by omega
  rcases hr with h | h | h | h <;> rw [h] <;> decide

/-- Truncation of `c7` to `[-(7N+1), 7N+6]`. -/
def tr (N : Nat) (p : Int) : Bool := c7 p && decide (-(7 * (N : Int) + 1) ≤ p) && decide (p ≤ 7 * (N : Int) + 6)

theorem tr_lo (N : Nat) : tr N (-(7 * (N : Int) + 1)) = true := by
  unfold tr c7
  have : (-(7 * (N : Int) + 1) + 1) % 7 = 0 := by omega
  simp [this] <;> omega

theorem tr_hi (N : Nat) : tr N (7 * (N : Int) + 6) = true := by
  unfold tr c7
  have : (7 * (N : Int) + 6 + 1) % 7 = 0 := by omega
  simp [this] <;> omega

theorem tr_below (N : Nat) (p : Int) (hp : p < -(7 * (N : Int) + 1)) : tr N p = false := by
  unfold tr
  have : ¬ (-(7 * (N : Int) + 1) ≤ p) := by omega
  simp [this]

theorem tr_above (N : Nat) (p : Int) (hp : 7 * (N : Int) + 6 < p) : tr N p = false := by
  unfold tr
  have : ¬ (p ≤ 7 * (N : Int) + 6) := by omega
  simp [this]

theorem tr_agree (N : Nat) (t : Nat) (p : Int) (h1 : -(7 * (N : Int) + 1) + t ≤ p) (h2 : p + t ≤ 7 * (N : Int) + 6) :
    evol (tr N) t p = evol c7 t p := by
  apply evol_local (a := -(7 * (N : Int) + 1)) (b := 7 * (N : Int) + 6) _ t p h1 h2
  intro q hq1 hq2
  unfold tr
  simp [hq1, hq2]

theorem tr_eq (N : Nat) (p : Int) :
    tr N p = if -(7 * (N : Int) + 1) ≤ p ∧ p ≤ 7 * (N : Int) + 6 then c7 p else false := by
  unfold tr
  by_cases h1 : -(7 * (N : Int) + 1) ≤ p <;> by_cases h2 : p ≤ 7 * (N : Int) + 6 <;> simp [h1, h2]

/-- Near the left end, the truncations are translates of each other. -/
theorem tr_left_shift (N m : Nat) (p : Int) (hp : p ≤ 7 * (N : Int) + 6) :
    tr (N + m) (p + (-(7 * (m : Int)))) = tr N p := by
  rw [tr_eq, tr_eq, show p + -(7 * (m : Int)) = p + 7 * (-(m : Int)) by omega, c7_shift]
  have e1 : (-(7 * ((N + m : Nat) : Int) + 1) ≤ p + 7 * (-(m : Int)) ∧
      p + 7 * (-(m : Int)) ≤ 7 * ((N + m : Nat) : Int) + 6) ↔
      (-(7 * (N : Int) + 1) ≤ p ∧ p ≤ 7 * (N : Int) + 6) := by push_cast; omega
  by_cases h : -(7 * (N : Int) + 1) ≤ p ∧ p ≤ 7 * (N : Int) + 6
  · rw [if_pos h, if_pos (e1.2 h)]
  · rw [if_neg h, if_neg (fun h' => h (e1.1 h'))]

theorem tr_right_shift (N m : Nat) (p : Int) (hp : -(7 * (N : Int) + 1) ≤ p) :
    tr (N + m) (p + 7 * (m : Int)) = tr N p := by
  rw [tr_eq, tr_eq, c7_shift]
  have e1 : (-(7 * ((N + m : Nat) : Int) + 1) ≤ p + 7 * (m : Int) ∧
      p + 7 * (m : Int) ≤ 7 * ((N + m : Nat) : Int) + 6) ↔
      (-(7 * (N : Int) + 1) ≤ p ∧ p ≤ 7 * (N : Int) + 6) := by push_cast; omega
  by_cases h : -(7 * (N : Int) + 1) ≤ p ∧ p ≤ 7 * (N : Int) + 6
  · rw [if_pos h, if_pos (e1.2 h)]
  · rw [if_neg h, if_neg (fun h' => h (e1.1 h'))]

/-! ## Windows and the certificate -/

def cw (w : Nat) (x : Int → Bool) : List Bool := (List.range (2 * w + 1)).map fun (i : Nat) => x ((i : Int) - (w : Int))
def le (e : Nat) (x : Int → Bool) (lo : Int) : List Bool := (List.range e).map fun (i : Nat) => x (lo + (i : Int))
def re (e : Nat) (x : Int → Bool) (hi : Int) : List Bool := (List.range e).map fun (i : Nat) => x (hi - (i : Int))

/-- A ranking certificate through (leftmost black position, rightmost black position, center window,
left-edge window, right-edge window): strict decrease at every step where the center column flips. -/
def JointCert (w e : Nat) (R : Int → Int → List Bool → List Bool → List Bool → Nat) : Prop :=
  ∀ (x : Int → Bool) (lo hi : Int), x lo = true → x hi = true → (∀ p, p < lo → x p = false) →
    (∀ p, hi < p → x p = false) → evol x 1 0 = !evol x 0 0 →
    R (lo - 1) (hi + 1) (cw w (fun p => evol x 1 p)) (le e (fun p => evol x 1 p) (lo - 1))
        (re e (fun p => evol x 1 p) (hi + 1)) <
      R lo hi (cw w x) (le e x lo) (re e x hi)

theorem map_range_congr {f g : Nat → Bool} {n : Nat} (h : ∀ i, i < n → f i = g i) :
    (List.range n).map f = (List.range n).map g := by
  apply List.map_congr_left
  intro i hi
  exact h i (List.mem_range.1 hi)

/-- Left-edge windows of the truncations do not depend on `N`. -/
theorem le_indep (e N m t : Nat) (he : e ≤ 14 * N + 7) :
    le e (fun p => evol (tr (N + m)) t p) (-(7 * ((N + m : Nat) : Int) + 1) - t) =
      le e (fun p => evol (tr N) t p) (-(7 * (N : Int) + 1) - t) := by
  unfold le
  apply map_range_congr
  intro i hi
  have := evol_local_le (x := tr N) (x' := tr (N + m)) (d := -(7 * (m : Int))) (b := 7 * (N : Int) + 6)
    (fun p hp => tr_left_shift N m p hp) t (-(7 * (N : Int) + 1) - t + i) (by omega)
  rw [show -(7 * (N : Int) + 1) - ↑t + ↑i + -(7 * (m : Int)) = -(7 * ((N + m : Nat) : Int) + 1) - ↑t + ↑i by
    push_cast; omega] at this
  exact this

/-- Right-edge windows of the truncations do not depend on `N`. -/
theorem re_indep (e N m t : Nat) (he : e ≤ 14 * N + 7) :
    re e (fun p => evol (tr (N + m)) t p) (7 * ((N + m : Nat) : Int) + 6 + t) =
      re e (fun p => evol (tr N) t p) (7 * (N : Int) + 6 + t) := by
  unfold re
  apply map_range_congr
  intro i hi
  have := evol_local_ge (x := tr N) (x' := tr (N + m)) (d := 7 * (m : Int)) (a := -(7 * (N : Int) + 1))
    (fun p hp => tr_right_shift N m p hp) t (7 * (N : Int) + 6 + t - i) (by omega)
  rw [show 7 * (N : Int) + 6 + ↑t - ↑i + 7 * (m : Int) = 7 * ((N + m : Nat) : Int) + 6 + ↑t - ↑i by
    push_cast; omega] at this
  exact this

/-- Center windows of the truncations follow the periodic configuration while the light cone allows. -/
theorem cw_agree (w N t : Nat) (h : t + w ≤ 7 * N + 1) :
    cw w (fun p => evol (tr N) t p) = cw w (fun p => evol c7 t p) := by
  unfold cw
  apply map_range_congr
  intro i hi
  exact tr_agree N t _ (by omega) (by omega)

/-- The ranked quantity along the run of `tr N`. -/
def S (w e : Nat) (R : Int → Int → List Bool → List Bool → List Bool → Nat) (N t : Nat) : Nat :=
  R (-(7 * (N : Int) + 1) - t) (7 * (N : Int) + 6 + t) (cw w (fun p => evol (tr N) t p))
    (le e (fun p => evol (tr N) t p) (-(7 * (N : Int) + 1) - t)) (re e (fun p => evol (tr N) t p) (7 * (N : Int) + 6 + t))

theorem S_step {w e : Nat} {R : Int → Int → List Bool → List Bool → List Bool → Nat} (hR : JointCert w e R)
    (N t : Nat) (ht : t + 1 ≤ 7 * N + 1) : S w e R N (t + 1) < S w e R N t := by
  have hl := left_edge (x := tr N) (lo := -(7 * (N : Int) + 1)) (tr_lo N) (fun p hp => tr_below N p hp) t
  have hr := right_edge (x := tr N) (hi := 7 * (N : Int) + 6) (tr_hi N) (fun p hp => tr_above N p hp) t
  have halt : evol (fun p => evol (tr N) t p) 1 0 = !evol (fun p => evol (tr N) t p) 0 0 := by
    simp only [evol_restart, Nat.add_zero]
    rw [tr_agree N (t + 1) 0 (by omega) (by omega), tr_agree N t 0 (by omega) (by omega)]
    exact c7_center t
  have h := hR (fun p => evol (tr N) t p) (-(7 * (N : Int) + 1) - t) (7 * (N : Int) + 6 + t) hl.1 hr.1 hl.2 hr.2 halt
  have hfun : (fun p => evol (fun p => evol (tr N) t p) 1 p) = (fun p => evol (tr N) (t + 1) p) := by
    funext p; rw [evol_restart]
  rw [hfun, show -(7 * (N : Int) + 1) - ↑t - 1 = -(7 * (N : Int) + 1) - ↑(t + 1) by push_cast; omega,
    show 7 * (N : Int) + 6 + ↑t + 1 = 7 * (N : Int) + 6 + ↑(t + 1) by push_cast; omega] at h
  exact h

theorem S_chain {w e : Nat} {R : Int → Int → List Bool → List Bool → List Bool → Nat} (hR : JointCert w e R)
    (N t : Nat) : ∀ d, t + d ≤ 7 * N + 1 → S w e R N (t + d) + d ≤ S w e R N t := by
  intro d
  induction d with
  | zero => intro _; simp
  | succ d ih =>
    intro hd
    have h1 := ih (by omega)
    have h2 := S_step hR N (t + d) (by omega)
    rw [show t + (d + 1) = t + d + 1 by omega]
    omega

theorem no_joint_local_ranking (w e : Nat) (R : Int → Int → List Bool → List Bool → List Bool → Nat) :
    ¬ JointCert w e R := by
  intro hR
  let N0 := e + 1
  have hN0 : N0 = e + 1 := rfl
  -- edge data of the reference run at times 28 i
  let a : Nat → List Bool := fun i =>
    le e (fun p => evol (tr N0) (28 * i) p) (-(7 * (N0 : Int) + 1) - (28 * i : Nat)) ++
      re e (fun p => evol (tr N0) (28 * i) p) (7 * (N0 : Int) + 6 + (28 * i : Nat))
  obtain ⟨i1, i2, hlt, -, ha⟩ := pigeonhole (e + e) a (fun i => by simp [a, le, re])
  have hlen : ∀ i, (le e (fun p => evol (tr N0) (28 * i) p) (-(7 * (N0 : Int) + 1) - (28 * i : Nat))).length = e :=
    fun i => by simp [le]
  have hsplit := List.append_inj ha (by rw [hlen, hlen])
  let t1 := 28 * i1
  let Δ := i2 - i1
  have ht2 : 28 * i2 = t1 + 28 * Δ := by omega
  -- the key periodicity: state of run N at time 28 i2 = state of run N + 4Δ at time t1
  have key : ∀ m, 28 * i2 + w ≤ 7 * (N0 + m) + 1 →
      S w e R (N0 + m) (28 * i2) = S w e R (N0 + m + 4 * Δ) t1 := by
    intro m hm
    unfold S
    have e1 : -(7 * ((N0 + m : Nat) : Int) + 1) - ((28 * i2 : Nat) : Int) =
        -(7 * ((N0 + m + 4 * Δ : Nat) : Int) + 1) - (t1 : Int) := by
      rw [ht2]; push_cast; omega
    have e2 : 7 * ((N0 + m : Nat) : Int) + 6 + ((28 * i2 : Nat) : Int) =
        7 * ((N0 + m + 4 * Δ : Nat) : Int) + 6 + (t1 : Int) := by
      rw [ht2]; push_cast; omega
    have ecw : cw w (fun p => evol (tr (N0 + m)) (28 * i2) p) = cw w (fun p => evol (tr (N0 + m + 4 * Δ)) t1 p) := by
      rw [cw_agree w (N0 + m) (28 * i2) hm, cw_agree w (N0 + m + 4 * Δ) t1 (by omega)]
      have : (fun p => evol c7 (28 * i2) p) = (fun p => evol c7 t1 p) := by
        funext p; rw [ht2, show t1 + 28 * Δ = t1 + 4 * (7 * Δ) by omega, evol_c7_period_mul]
      rw [this]
    have ele : le e (fun p => evol (tr (N0 + m)) (28 * i2) p) (-(7 * ((N0 + m : Nat) : Int) + 1) - ((28 * i2 : Nat) : Int)) =
        le e (fun p => evol (tr (N0 + m + 4 * Δ)) t1 p) (-(7 * ((N0 + m + 4 * Δ : Nat) : Int) + 1) - (t1 : Int)) := by
      rw [le_indep e N0 m (28 * i2) (by omega), show N0 + m + 4 * Δ = N0 + (m + 4 * Δ) by omega,
        le_indep e N0 (m + 4 * Δ) t1 (by omega)]
      exact hsplit.1.symm
    have ere : re e (fun p => evol (tr (N0 + m)) (28 * i2) p) (7 * ((N0 + m : Nat) : Int) + 6 + ((28 * i2 : Nat) : Int)) =
        re e (fun p => evol (tr (N0 + m + 4 * Δ)) t1 p) (7 * ((N0 + m + 4 * Δ : Nat) : Int) + 6 + (t1 : Int)) := by
      rw [re_indep e N0 m (28 * i2) (by omega), show N0 + m + 4 * Δ = N0 + (m + 4 * Δ) by omega,
        re_indep e N0 (m + 4 * Δ) t1 (by omega)]
      exact hsplit.2.symm
    rw [ecw, ele, ere, e1, e2]
  -- descent
  let M0 := 28 * i2 + w
  let f : Nat → Nat := fun m => S w e R (N0 + m) t1
  have period : ∀ m, M0 ≤ m → f (m + 4 * Δ) + 28 * Δ ≤ f m := by
    intro m hm
    have hc := S_chain hR (N0 + m) t1 (28 * Δ) (by omega)
    rw [← ht2, key m (by omega), show N0 + m + 4 * Δ = N0 + (m + 4 * Δ) by omega] at hc
    exact hc
  have descent : ∀ k, f (M0 + k * (4 * Δ)) + k * (28 * Δ) ≤ f M0 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have h := period (M0 + k * (4 * Δ)) (by omega)
      rw [show M0 + k * (4 * Δ) + 4 * Δ = M0 + (k + 1) * (4 * Δ) by rw [Nat.succ_mul k (4 * Δ)]; omega] at h
      rw [Nat.succ_mul k (28 * Δ)]
      omega
  have := descent (f M0 + 1)
  have hΔ : 1 ≤ 28 * Δ := by omega
  have : f M0 + 1 ≤ (f M0 + 1) * (28 * Δ) := Nat.le_mul_of_pos_right _ hΔ
  omega

end JointBarrier

#print axioms JointBarrier.no_joint_local_ranking

#print axioms JointBarrier.c7_center
