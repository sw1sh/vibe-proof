import Ruliology.CellularAutomata.Rule30Jen

/-!
# Period-2 program, zero-boundary left half (ZBL): barriers for invariant / ranking-function proofs

`z s t k` is rule 30 on the left half with column 0 forced white ("zero-boundary left half"),
indexed by depth `k` (cell `p = -k`; depth `0` is the white wall), started from the state `s` at time 0.
Q_01 asks: no finitely supported start keeps column -1 (depth 1) black at every even time.

* `trunc_survives`: the truncated stripe `trunc n` (black at odd depths `≤ n`, `n` odd) keeps depth 1
  black at every time `t ≤ n` and turns it white at time `n + 1`. So constrained runs from finite
  starts have unbounded length.
* `finite_abstraction_has_lasso` (barrier B1): every abstraction of states into bit-lists of a fixed
  length repeats a value along one surviving constrained run; so no finite-state abstraction can prove
  termination of the constrained ZBL.
* `no_local_ranking` (barrier B2): no function `R (width) (wall window) (edge window)` into `Nat`
  strictly decreases along every surviving double step of every finite start.
-/

namespace ZBLBarrier

/-- Zero-boundary left half: depth `k ≥ 1`, wall at depth 0. -/
def z (s : Nat → Bool) : Nat → Nat → Bool
  | 0, k => if k = 0 then false else s k
  | t + 1, k => if k = 0 then false else xor (z s t (k + 1)) (z s t k || z s t (k - 1))

theorem z_wall (s : Nat → Bool) (t : Nat) : z s t 0 = false := by
  cases t <;> simp [z]

theorem z_zero {s : Nat → Bool} {k : Nat} (hk : k ≠ 0) : z s 0 k = s k := by
  simp [z, hk]

theorem z_succ {s : Nat → Bool} {t k : Nat} (hk : k ≠ 0) :
    z s (t + 1) k = xor (z s t (k + 1)) (z s t k || z s t (k - 1)) := by
  simp [z, hk]

/-- Restarting from the state at time `a` is the same run (semigroup property). -/
theorem z_restart (s : Nat → Bool) (a : Nat) : ∀ b k, z (fun k => z s a k) b k = z s (a + b) k := by
  intro b
  induction b with
  | zero =>
    intro k
    by_cases hk : k = 0
    · subst hk; rw [z_wall, z_wall]
    · rw [z_zero hk]; rfl
  | succ b ih =>
    intro k
    by_cases hk : k = 0
    · subst hk; rw [z_wall, z_wall]
    · rw [z_succ hk, show a + (b + 1) = (a + b) + 1 by omega, z_succ hk, ih, ih, ih]

/-- The infinite stripe: black exactly at odd depths. -/
def stripe (k : Nat) : Bool := k % 2 == 1

theorem stripe_step (k : Nat) (hk : k ≠ 0) :
    xor (stripe (k + 1)) (stripe k || stripe (k - 1)) = stripe k := by
  unfold stripe
  rcases Nat.mod_two_eq_zero_or_one k with h | h
  · have h1 : (k + 1) % 2 = 1 := by omega
    have h2 : (k - 1) % 2 = 1 := by omega
    simp [h, h1, h2]
  · have h1 : (k + 1) % 2 = 0 := by omega
    simp [h, h1]

/-- The stripe is a fixed point of the ZBL. -/
theorem stripe_fixed : ∀ t k, z stripe t k = stripe k := by
  intro t
  induction t with
  | zero =>
    intro k
    by_cases hk : k = 0
    · subst hk; rw [z_wall]; rfl
    · exact z_zero hk
  | succ t ih =>
    intro k
    by_cases hk : k = 0
    · subst hk; rw [z_wall]; rfl
    · rw [z_succ hk, ih, ih, ih, stripe_step k hk]

/-- Truncated stripe of width `n`. -/
def trunc (n : Nat) (k : Nat) : Bool := stripe k && decide (k ≤ n)

theorem trunc_width {n : Nat} (hn : n % 2 = 1) : trunc n n = true ∧ ∀ k, n < k → trunc n k = false := by
  refine ⟨?_, fun k hk => ?_⟩
  · simp [trunc, stripe, hn]
  · simp [trunc]; omega

/-- Inside the light cone of the untouched region the truncated stripe evolves as the stripe. -/
theorem trunc_agree {n : Nat} (hn : n % 2 = 1) :
    ∀ t k, k + t ≤ n + 1 → z (trunc n) t k = stripe k := by
  intro t
  induction t with
  | zero =>
    intro k hk
    by_cases h0 : k = 0
    · subst h0; rw [z_wall]; rfl
    · rw [z_zero h0]
      by_cases hle : k ≤ n
      · simp [trunc, hle]
      · have hk' : k = n + 1 := by omega
        subst hk'
        have : (n + 1) % 2 = 0 := by omega
        simp [trunc, stripe, this]
  | succ t ih =>
    intro k hk
    by_cases h0 : k = 0
    · subst h0; rw [z_wall]; rfl
    · rw [z_succ h0, ih (k + 1) (by omega), ih k (by omega), ih (k - 1) (by omega), stripe_step k h0]

/-- On the next anti-diagonal the truncated stripe is the complement of the stripe. -/
theorem trunc_antidiag {n : Nat} (hn : n % 2 = 1) :
    ∀ t k, k ≠ 0 → k + t = n + 2 → z (trunc n) t k = !stripe k := by
  intro t
  induction t with
  | zero =>
    intro k h0 hk
    rw [z_zero h0]
    have hk' : k = n + 2 := by omega
    subst hk'
    have : (n + 2) % 2 = 1 := by omega
    simp [trunc, stripe, this]
  | succ t ih =>
    intro k h0 hk
    rw [z_succ h0, ih (k + 1) (by omega) (by omega), trunc_agree hn t k (by omega),
      trunc_agree hn t (k - 1) (by omega)]
    have := stripe_step k h0
    revert this
    cases stripe (k + 1) <;> cases stripe k <;> cases stripe (k - 1) <;> simp

/-- **Unbounded survival.** For odd `n`, depth 1 is black at every time `t ≤ n` and white at time `n + 1`
(an even time): the constrained run from the finite start `trunc n` lives exactly through time `n`. -/
theorem trunc_survives {n : Nat} (hn : n % 2 = 1) :
    (∀ t, t ≤ n → z (trunc n) t 1 = true) ∧ z (trunc n) (n + 1) 1 = false := by
  refine ⟨fun t ht => ?_, ?_⟩
  · rw [trunc_agree hn t 1 (by omega)]; rfl
  · rw [trunc_antidiag hn (n + 1) 1 (by omega) (by omega)]; rfl

/-! ## Barrier B1: finite abstractions -/

/-- The state after `j` double steps. -/
def iter (s : Nat → Bool) (j : Nat) : Nat → Bool := fun k => z s (2 * j) k

/-- A double step `s ↦ G s` survives when depth 1 is black at times 0 and 2. -/
def Survives (s : Nat → Bool) : Prop := z s 0 1 = true ∧ z s 2 1 = true

theorem iter_survives {n : Nat} (hn : n % 2 = 1) {j : Nat} (hj : 2 * j + 2 ≤ n) :
    Survives (iter (trunc n) j) := by
  unfold Survives iter
  rw [z_restart, z_restart]
  exact ⟨(trunc_survives hn).1 _ (by omega), (trunc_survives hn).1 _ (by omega)⟩

/-- **B1.** Any abstraction `α` of states into bit-lists of length `w` (i.e. any abstraction with at most
`2^w` abstract states) takes the same value twice along one run of surviving double steps from a finite
start. Hence the abstract transition graph has a cycle through surviving transitions, and no finite-state
abstraction can certify that every constrained run from a finite start terminates. -/
theorem finite_abstraction_has_lasso (w : Nat) (α : (Nat → Bool) → List Bool) (hα : ∀ s, (α s).length = w) :
    ∃ n m m', n % 2 = 1 ∧ m < m' ∧ (∀ j, j ≤ m' → Survives (iter (trunc n) j)) ∧
      α (iter (trunc n) m) = α (iter (trunc n) m') := by
  obtain ⟨m, m', hlt, hle, heq⟩ := Ruliology.CellularAutomata.Rule30Jen.pigeonhole w (fun j => α (iter (trunc (2 * 2 ^ w + 3)) j))
    (fun j => hα _)
  refine ⟨2 * 2 ^ w + 3, m, m', by omega, hlt, fun j hj => iter_survives (by omega) (by omega), heq⟩

/-! ## Barrier B2: rankings through width, wall window and edge window -/

/-- The edge moves out one depth per step. -/
theorem z_width {s : Nat → Bool} {W : Nat} (hW : 1 ≤ W) (h1 : s W = true) (h0 : ∀ k, W < k → s k = false) :
    ∀ t, z s t (W + t) = true ∧ ∀ k, W + t < k → z s t k = false := by
  intro t
  induction t with
  | zero =>
    refine ⟨?_, fun k hk => ?_⟩
    · rw [Nat.add_zero, z_zero (by omega), h1]
    · rw [z_zero (by omega), h0 k (by omega)]
  | succ t ih =>
    refine ⟨?_, fun k hk => ?_⟩
    · rw [z_succ (by omega), ih.2 _ (by omega), ih.2 _ (by omega),
        show W + (t + 1) - 1 = W + t by omega, ih.1]; rfl
    · rw [z_succ (by omega), ih.2 _ (by omega), ih.2 _ (by omega), ih.2 _ (by omega)]; rfl

/-- Translation invariance away from the wall. -/
theorem z_shift {s s' : Nat → Bool} {d a : Nat} (ha : 1 ≤ a) (h : ∀ k, a ≤ k → s' (k + d) = s k) :
    ∀ t k, a + t ≤ k → z s' t (k + d) = z s t k := by
  intro t
  induction t with
  | zero =>
    intro k hk
    rw [z_zero (by omega), z_zero (by omega), h k (by omega)]
  | succ t ih =>
    intro k hk
    rw [z_succ (by omega), z_succ (by omega), show k + d + 1 = (k + 1) + d by omega,
      show k + d - 1 = (k - 1) + d by omega, ih (k + 1) (by omega), ih k (by omega), ih (k - 1) (by omega)]

theorem trunc_shift (n m k : Nat) : trunc (n + 2 * m) (k + 2 * m) = trunc n k := by
  unfold trunc stripe
  have h1 : (k + 2 * m) % 2 = k % 2 := by omega
  rw [h1]
  by_cases hk : k ≤ n
  · have : k + 2 * m ≤ n + 2 * m := by omega
    simp [hk, this]
  · have : ¬ (k + 2 * m ≤ n + 2 * m) := by omega
    simp [hk, this]

/-- Wall window (depths `1..w`) and edge window (depths `W, W-1, ..., W-e+1`). -/
def wallW (w : Nat) (s : Nat → Bool) : List Bool := (List.range w).map fun i => s (i + 1)
def edgeW (e : Nat) (s : Nat → Bool) (W : Nat) : List Bool := (List.range e).map fun i => s (W - i)

theorem map_range_congr {f g : Nat → Bool} {n : Nat} (h : ∀ i, i < n → f i = g i) :
    (List.range n).map f = (List.range n).map g := by
  apply List.map_congr_left
  intro i hi
  exact h i (List.mem_range.1 hi)

/-- A ranking certificate through (width, wall window, edge window): strict decrease along every
surviving double step of every finitely supported start of width `W`. -/
def Cert (w e : Nat) (R : Nat → List Bool → List Bool → Nat) : Prop :=
  ∀ (s : Nat → Bool) (W : Nat), 1 ≤ W → s W = true → (∀ k, W < k → s k = false) → Survives s →
    R (W + 2) (wallW w (fun k => z s 2 k)) (edgeW e (fun k => z s 2 k) (W + 2)) < R W (wallW w s) (edgeW e s W)

theorem iter_succ (s : Nat → Bool) (j : Nat) : (fun k => z (iter s j) 2 k) = iter s (j + 1) := by
  funext k
  unfold iter
  rw [z_restart, show 2 * j + 2 = 2 * (j + 1) by omega]

theorem wall_iter {n : Nat} (hn : n % 2 = 1) (w j : Nat) (h : 2 * j + w ≤ n + 1) :
    wallW w (iter (trunc n) j) = wallW w stripe := by
  unfold wallW iter
  exact map_range_congr fun i hi => trunc_agree hn _ _ (by omega)

theorem edge_iter (n0 m e j : Nat) (he : e ≤ n0) :
    edgeW e (iter (trunc (n0 + 2 * m)) j) (n0 + 2 * m + 2 * j) = edgeW e (iter (trunc n0) j) (n0 + 2 * j) := by
  unfold edgeW iter
  apply map_range_congr
  intro i hi
  rw [show n0 + 2 * m + 2 * j - i = (n0 + 2 * j - i) + 2 * m by omega]
  exact z_shift (s := trunc n0) (s' := trunc (n0 + 2 * m)) (d := 2 * m) (a := 1) (by omega)
    (fun k _ => trunc_shift n0 m k) (2 * j) (n0 + 2 * j - i) (by omega)

/-- **B2.** No function of (width, wall window of any size `w`, edge window of any size `e`) can be a ranking
function certifying termination of the constrained ZBL from all finite starts. -/
theorem no_local_ranking (w e : Nat) (R : Nat → List Bool → List Bool → Nat) : ¬ Cert w e R := by
  intro hR
  let n0 := 2 * e + 1
  have hn0 : n0 % 2 = 1 := by omega
  let E : Nat → List Bool := fun j => edgeW e (iter (trunc n0) j) (n0 + 2 * j)
  obtain ⟨j1, j2, hlt, -, hE⟩ := Ruliology.CellularAutomata.Rule30Jen.pigeonhole e E
    (fun j => by simp [E, edgeW])
  let S := wallW w stripe
  let N0 := 2 * j2 + w + 2
  -- one run, from j1 to j2
  have stepR : ∀ m, N0 ≤ m → ∀ j, j < j2 →
      R (n0 + 2 * m + 2 * (j + 1)) S (E (j + 1)) < R (n0 + 2 * m + 2 * j) S (E j) := by
    intro m hm j hj
    have hn : (n0 + 2 * m) % 2 = 1 := by omega
    have hw := z_width (s := trunc (n0 + 2 * m)) (W := n0 + 2 * m) (by omega)
      (trunc_width hn).1 (trunc_width hn).2 (2 * j)
    have hstep := hR (iter (trunc (n0 + 2 * m)) j) (n0 + 2 * m + 2 * j) (by omega) hw.1 hw.2
      (iter_survives hn (by omega))
    rw [iter_succ, wall_iter hn w (j + 1) (by omega), wall_iter hn w j (by omega),
      show n0 + 2 * m + 2 * j + 2 = n0 + 2 * m + 2 * (j + 1) by omega, edge_iter n0 m e (j + 1) (by omega),
      edge_iter n0 m e j (by omega)] at hstep
    exact hstep
  have chain : ∀ m, N0 ≤ m → ∀ i, i ≤ j2 - j1 →
      R (n0 + 2 * m + 2 * (j1 + i)) S (E (j1 + i)) + i ≤ R (n0 + 2 * m + 2 * j1) S (E j1) := by
    intro m hm i
    induction i with
    | zero => intro _; simp
    | succ i ih =>
      intro hi
      have ih' := ih (by omega)
      have h := stepR m hm (j1 + i) (by omega)
      rw [show j1 + (i + 1) = j1 + i + 1 by omega]
      omega
  let P := j2 - j1
  have hP : 1 ≤ P := by omega
  let f : Nat → Nat := fun M => R M S (E j1)
  have period : ∀ m, N0 ≤ m → f (n0 + 2 * m + 2 * j1 + 2 * P) + P ≤ f (n0 + 2 * m + 2 * j1) := by
    intro m hm
    have h := chain m hm P (Nat.le_refl _)
    rw [show j1 + P = j2 by omega, ← hE, show n0 + 2 * m + 2 * j2 = n0 + 2 * m + 2 * j1 + 2 * P by omega] at h
    exact h
  let B := n0 + 2 * N0 + 2 * j1
  have descent : ∀ k, f (B + 2 * (k * P)) + k * P ≤ f B := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have e1 : (k + 1) * P = k * P + P := Nat.succ_mul k P
      have h := period (N0 + k * P) (by omega)
      have e2 : n0 + 2 * (N0 + k * P) + 2 * j1 = B + 2 * (k * P) := by omega
      have e3 : B + 2 * ((k + 1) * P) = B + 2 * (k * P) + 2 * P := by rw [e1]; omega
      rw [e2] at h
      rw [e3, e1]
      omega
  have := descent (f B + 1)
  have hk : f B + 1 ≤ (f B + 1) * P := Nat.le_mul_of_pos_right _ hP
  omega

end ZBLBarrier

/-! ## Independent verification extensions (verify-A2-rigor) -/
namespace ZBLBarrier

/-- General pigeonhole: a sequence with values in a list `L` repeats within `L.length + 1` terms. -/
theorem pigeonhole_gen {A : Type} (L : List A) (f : Nat → A) (hf : ∀ m, f m ∈ L) :
    ∃ m n, m < n ∧ n ≤ L.length ∧ f m = f n := by
  classical
  refine Classical.byContradiction fun hne => ?_
  have hinj : ∀ m ∈ List.range (L.length + 1), ∀ n ∈ List.range (L.length + 1), f m = f n → m = n := by
    intro m hm n hn e
    simp only [List.mem_range] at hm hn
    rcases Nat.lt_trichotomy m n with h | h | h
    · exact absurd ⟨m, n, h, by omega, e⟩ hne
    · exact h
    · exact absurd ⟨n, m, h, by omega, e.symm⟩ hne
  have hnd := Ruliology.CellularAutomata.Rule30Jen.nodup_map_of_inj f List.nodup_range hinj
  have := Ruliology.CellularAutomata.Rule30Jen.length_le_of_subset hnd fun x hx => by
    obtain ⟨m, -, rfl⟩ := List.mem_map.1 hx
    exact hf m
  simp only [List.length_map, List.length_range] at this
  omega

/-- B1 for an abstraction into ANY finite set of abstract values (listed by `L`). -/
theorem finite_abstraction_has_lasso_gen {A : Type} (L : List A) (α : (Nat → Bool) → A)
    (hα : ∀ s, α s ∈ L) :
    ∃ n m m', n % 2 = 1 ∧ m < m' ∧ (∀ j, j ≤ m' → Survives (iter (trunc n) j)) ∧
      α (iter (trunc n) m) = α (iter (trunc n) m') := by
  obtain ⟨m, m', hlt, hle, heq⟩ :=
    pigeonhole_gen L (fun j => α (iter (trunc (2 * L.length + 3)) j)) (fun j => hα _)
  exact ⟨2 * L.length + 3, m, m', by omega, hlt, fun j hj => iter_survives (by omega) (by omega), heq⟩

/-- Reflexive-transitive closure (core Lean lacks `Relation.ReflTransGen`). -/
inductive RTG {A : Type} (R : A → A → Prop) : A → A → Prop
  | refl (a : A) : RTG R a a
  | tail {a b c : A} : RTG R a b → R b c → RTG R a c

/-- One double step. -/
def G (s : Nat → Bool) : Nat → Bool := fun k => z s 2 k

theorem iter_G (s : Nat → Bool) (j : Nat) : iter s (j + 1) = G (iter s j) := by
  unfold G; rw [iter_succ]

theorem iter_zero_trunc (n : Nat) : iter (trunc n) 0 = trunc n := by
  funext k
  unfold iter
  by_cases hk : k = 0
  · subst hk; rw [z_wall]; rfl
  · simp only [Nat.mul_zero]; exact z_zero hk

/-- Every state on the run is finitely supported. -/
theorem iter_finite {n : Nat} (hn : n % 2 = 1) (j : Nat) : ∀ k, n + 2 * j < k → iter (trunc n) j k = false := by
  intro k hk
  exact (z_width (s := trunc n) (W := n) (by omega) (trunc_width hn).1 (trunc_width hn).2 (2 * j)).2 k hk

/-- "Consequently": every abstract transition relation that is sound for surviving double steps between
finitely supported states has a cycle reachable from the image of a finite start. -/
theorem sound_abstraction_has_reachable_cycle {A : Type} (L : List A) (α : (Nat → Bool) → A)
    (hα : ∀ s, α s ∈ L) (R : A → A → Prop)
    (hR : ∀ s, (∃ W, ∀ k, W < k → s k = false) → Survives s → R (α s) (α (G s))) :
    ∃ n, n % 2 = 1 ∧ (∀ k, n < k → trunc n k = false) ∧
      ∃ a, RTG R (α (trunc n)) a ∧ Relation.TransGen R a a := by
  obtain ⟨n, m, m', hn, hlt, hsurv, heq⟩ := finite_abstraction_has_lasso_gen L α hα
  have step : ∀ j, j < m' → R (α (iter (trunc n) j)) (α (iter (trunc n) (j + 1))) := by
    intro j hj
    rw [iter_G]
    exact hR _ ⟨n + 2 * j, iter_finite hn j⟩ (hsurv j (by omega))
  have reach : ∀ j, j ≤ m' → RTG R (α (trunc n)) (α (iter (trunc n) j)) := by
    intro j
    induction j with
    | zero => intro _; rw [iter_zero_trunc]; exact RTG.refl _
    | succ j ih => intro hj; exact RTG.tail (ih (by omega)) (step j (by omega))
  have cyc : ∀ i, 1 ≤ i → m + i ≤ m' →
      Relation.TransGen R (α (iter (trunc n) m)) (α (iter (trunc n) (m + i))) := by
    intro i
    induction i with
    | zero => intro h; omega
    | succ i ih =>
      intro _ hi
      by_cases h0 : i = 0
      · subst h0; exact Relation.TransGen.single (step m (by omega))
      · refine Relation.TransGen.tail (ih (by omega) (by omega)) ?_
        rw [show m + (i + 1) = (m + i) + 1 by omega]
        exact step (m + i) (by omega)
  refine ⟨n, hn, (trunc_width hn).2, α (iter (trunc n) m), reach m (by omega), ?_⟩
  have h := cyc (m' - m) (by omega) (by omega)
  rw [show m + (m' - m) = m' by omega, ← heq] at h
  exact h

/-- No ranking function through a finite abstraction decreases along all surviving double steps
between finitely supported states. -/
theorem no_finite_abstract_ranking {A : Type} (L : List A) (α : (Nat → Bool) → A) (hα : ∀ s, α s ∈ L)
    (rank : A → Nat) :
    ¬ (∀ s, (∃ W, ∀ k, W < k → s k = false) → Survives s → rank (α (G s)) < rank (α s)) := by
  intro h
  obtain ⟨n, -, -, a, -, hc⟩ :=
    sound_abstraction_has_reachable_cycle L α hα (fun a b => rank b < rank a) h
  have key : ∀ x y, Relation.TransGen (fun a b => rank b < rank a) x y → rank y < rank x := by
    intro x y hxy
    induction hxy with
    | single h => exact h
    | tail _ h ih => exact Nat.lt_trans h ih
  exact Nat.lt_irrefl _ (key a a hc)

/-- Sanity: the double step from `G^(2^w+1) trunc_n` with `n = 2·2^w+3` does NOT survive
(the prose "j ≤ 2^w + 1" is off by one; the Lean proof only needs `j ≤ 2^w`). -/
theorem prose_off_by_one (w : Nat) : ¬ Survives (iter (trunc (2 * 2 ^ w + 3)) (2 ^ w + 1)) := by
  intro h
  have hn : (2 * 2 ^ w + 3) % 2 = 1 := by omega
  have h2 := h.2
  unfold iter at h2
  rw [z_restart, show 2 * (2 ^ w + 1) + 2 = (2 * 2 ^ w + 3) + 1 by omega, (trunc_survives hn).2] at h2
  exact Bool.false_ne_true h2

end ZBLBarrier

#print axioms ZBLBarrier.finite_abstraction_has_lasso
#print axioms ZBLBarrier.finite_abstraction_has_lasso_gen
#print axioms ZBLBarrier.sound_abstraction_has_reachable_cycle
#print axioms ZBLBarrier.no_finite_abstract_ranking
#print axioms ZBLBarrier.prose_off_by_one

-- writeup-r2 axiom audit (appended)
#print axioms ZBLBarrier.finite_abstraction_has_lasso_gen
#print axioms ZBLBarrier.sound_abstraction_has_reachable_cycle
#print axioms ZBLBarrier.no_finite_abstract_ranking
#print axioms ZBLBarrier.prose_off_by_one
