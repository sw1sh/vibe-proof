/-!
Independent machine check of the "A1-reformulation" claim (q01-monovariant): the zero-boundary left half (ZBL)
of Rule 30 under the phase-0 period-2 constraint.

Coordinates: a row is `x : Nat → Bool`; `x k` (`k ≥ 1`) is the cell at depth `k` (i.e. `cell t (-k)`), and `x 0`
is the white wall.  One ZBL step is `step x 0 = false`, `step x (k+1) = x (k+2) xor (x (k+1) || x k)`.
The phase-0 constraint is `run x (2 s) 1 = true` for every `s`.

Claim objects: `col f = (1, f 0, 1, f 1, ...)`, `X 0 = 0`, `X 1 = col f`,
`X (k+1) t = X k (t+1) xor (X k t || X (k-1) t)`, `Theta f k = X k 0`.
-/

namespace A1ReformCheck

/-! ## ZBL dynamics -/

def step (x : Nat → Bool) : Nat → Bool
  | 0 => false
  | k + 1 => xor (x (k + 2)) (x (k + 1) || x k)

def run (x : Nat → Bool) : Nat → Nat → Bool
  | 0 => x
  | t + 1 => step (run x t)

theorem step_zero (x : Nat → Bool) : step x 0 = false := rfl
theorem step_succ (x : Nat → Bool) (k : Nat) :
    step x (k + 1) = xor (x (k + 2)) (x (k + 1) || x k) := rfl
theorem run_zero (x : Nat → Bool) : run x 0 = x := rfl
theorem run_succ (x : Nat → Bool) (t : Nat) : run x (t + 1) = step (run x t) := rfl

theorem run_add (x : Nat → Bool) (t i : Nat) : run x (t + i) = run (run x t) i := by
  induction i with
  | zero => rfl
  | succ i ih => rw [← Nat.add_assoc, run_succ, run_succ, ih]

theorem run_wall {x : Nat → Bool} (hw : x 0 = false) (t : Nat) : run x t 0 = false := by
  cases t with
  | zero => exact hw
  | succ t => rfl

/-- Light cone: `run x t k` depends only on `x 0, …, x (k+t)`. -/
theorem run_dep (t : Nat) : ∀ (x y : Nat → Bool) (k : Nat),
    (∀ i, i ≤ k + t → x i = y i) → run x t k = run y t k := by
  induction t with
  | zero => intro x y k h; exact h k (by omega)
  | succ t ih =>
    intro x y k h
    cases k with
    | zero => rfl
    | succ j =>
      rw [run_succ, run_succ, step_succ, step_succ,
        ih x y (j + 2) (fun i hi => h i (by omega)),
        ih x y (j + 1) (fun i hi => h i (by omega)),
        ih x y j (fun i hi => h i (by omega))]

/-- Left-permutive pivot of the forward evolution: for `k ≥ 1`, `run x t k = x (k+t) xor F(x 0..x (k+t-1))`. -/
theorem run_aff (t : Nat) : ∀ (x y : Nat → Bool) (k : Nat), 1 ≤ k →
    (∀ i, i < k + t → x i = y i) →
    xor (run x t k) (run y t k) = xor (x (k + t)) (y (k + t)) := by
  induction t with
  | zero => intro x y k _ _; rfl
  | succ t ih =>
    intro x y k hk h
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [run_succ, run_succ, step_succ, step_succ,
      run_dep t x y (j + 1) (fun i hi => h i (by omega)),
      run_dep t x y j (fun i hi => h i (by omega))]
    have key := ih x y (j + 2) (by omega) (fun i hi => h i (by omega))
    rw [show j + 1 + (t + 1) = j + 2 + t by omega, ← key]
    generalize run x t (j + 2) = a
    generalize run y t (j + 2) = b
    generalize (run y t (j + 1) || run y t j) = c
    cases a <;> cases b <;> cases c <;> rfl

/-! ## The column-pair diagram `X` and the map `Theta` -/

def X (c : Nat → Bool) : Nat → Nat → Bool
  | 0, _ => false
  | 1, t => c t
  | k + 2, t => xor (X c (k + 1) (t + 1)) (X c (k + 1) t || X c k t)

theorem X_zero (c : Nat → Bool) (t : Nat) : X c 0 t = false := by rw [X]
theorem X_one (c : Nat → Bool) (t : Nat) : X c 1 t = c t := by rw [X]
theorem X_add_two (c : Nat → Bool) (k t : Nat) :
    X c (k + 2) t = xor (X c (k + 1) (t + 1)) (X c (k + 1) t || X c k t) := by rw [X]

/-- `col f = (1, f 0, 1, f 1, …)`. -/
def col (f : Nat → Bool) (t : Nat) : Bool := if t % 2 = 0 then true else f (t / 2)

def Theta (f : Nat → Bool) (k : Nat) : Bool := X (col f) k 0

def shift (f : Nat → Bool) : Nat → Bool := fun s => f (s + 1)

/-- The spatial recurrence solved back for the time step (left-permutivity). -/
theorem X_succ_time (c : Nat → Bool) (j t : Nat) :
    X c (j + 1) (t + 1) = xor (X c (j + 2) t) (X c (j + 1) t || X c j t) := by
  rw [X_add_two]
  generalize X c (j + 1) (t + 1) = a
  generalize (X c (j + 1) t || X c j t) = b
  cases a <;> cases b <;> rfl

/-- Any column-1 sequence `c` (with column 0 the white wall) generates a diagram that is the forward ZBL
evolution of its own row 0. -/
theorem run_row0 (c : Nat → Bool) : ∀ t k, run (fun k => X c k 0) t k = X c k t := by
  intro t
  induction t with
  | zero => intro k; rfl
  | succ t ih =>
    intro k
    cases k with
    | zero => rw [X_zero]; rfl
    | succ j => rw [run_succ, step_succ, ih (j + 2), ih (j + 1), ih j, X_succ_time]

/-- Columns 0 (the wall) and 1 determine the whole forward evolution. -/
theorem X_col1 (x : Nat → Bool) (hw : x 0 = false) :
    ∀ k t, X (fun t => run x t 1) k t = run x t k := by
  have key : ∀ k, (∀ t, X (fun t => run x t 1) k t = run x t k) ∧
      (∀ t, X (fun t => run x t 1) (k + 1) t = run x t (k + 1)) := by
    intro k
    induction k with
    | zero => exact ⟨fun t => by rw [X_zero, run_wall hw], fun t => by rw [X_one]⟩
    | succ k ih =>
      refine ⟨ih.2, fun t => ?_⟩
      show X (fun t => run x t 1) (k + 2) t = run x t (k + 2)
      rw [X_add_two, ih.2 (t + 1), ih.2 t, ih.1 t, run_succ, step_succ]
      generalize run x t (k + 2) = a
      generalize (run x t (k + 1) || run x t k) = b
      cases a <;> cases b <;> rfl
  intro k t
  exact (key k).1 t

/-! ## Part (a) -/

def Constrained0 (x : Nat → Bool) : Prop := ∀ s, run x (2 * s) 1 = true

theorem col_eq (x : Nat → Bool) (h : Constrained0 x) :
    col (fun s => run x (2 * s + 1) 1) = fun t => run x t 1 := by
  funext t
  unfold col
  by_cases ht : t % 2 = 0
  · rw [if_pos ht]
    obtain ⟨s, rfl⟩ : ∃ s, t = 2 * s := ⟨t / 2, by omega⟩
    exact (h s).symm
  · rw [if_neg ht]
    obtain ⟨s, rfl⟩ : ∃ s, t = 2 * s + 1 := ⟨t / 2, by omega⟩
    show run x (2 * ((2 * s + 1) / 2) + 1) 1 = run x (2 * s + 1) 1
    rw [show (2 * s + 1) / 2 = s by omega]

/-- (a, ⇒): a row with a phase-0 constrained forward history is `Theta f` with `f s = x_1(2s+1)`. -/
theorem a_forward (x : Nat → Bool) (hw : x 0 = false) (h : Constrained0 x) :
    x = Theta (fun s => run x (2 * s + 1) 1) := by
  funext k
  unfold Theta
  rw [col_eq x h, X_col1 x hw k 0]
  rfl

/-- (a, ⇐): column 1 of the forward evolution of `Theta f` is `col f`. -/
theorem run_Theta_col1 (f : Nat → Bool) (t : Nat) : run (Theta f) t 1 = col f t := by
  have := run_row0 (col f) t 1
  rw [X_one] at this
  exact this

theorem Theta_wall (f : Nat → Bool) : Theta f 0 = false := X_zero _ _

theorem Theta_constrained (f : Nat → Bool) : Constrained0 (Theta f) := by
  intro s
  rw [run_Theta_col1]
  unfold col
  rw [if_pos (by omega)]

theorem Theta_free (f : Nat → Bool) (s : Nat) : run (Theta f) (2 * s + 1) 1 = f s := by
  rw [run_Theta_col1]
  unfold col
  rw [if_neg (by omega), show (2 * s + 1) / 2 = s by omega]

/-- **Part (a).** -/
theorem part_a (x : Nat → Bool) (hw : x 0 = false) :
    Constrained0 x ↔ ∃ f, x = Theta f := by
  constructor
  · intro h; exact ⟨_, a_forward x hw h⟩
  · rintro ⟨f, rfl⟩; exact Theta_constrained f

theorem part_a_namely (f x : Nat → Bool) (h : x = Theta f) (s : Nat) :
    f s = run x (2 * s + 1) 1 := by
  subst h; rw [Theta_free]

/-! ## Part (b) -/

theorem Theta_inj (f g : Nat → Bool) (h : ∀ k, 1 ≤ k → Theta f k = Theta g k) : f = g := by
  have hfg : Theta f = Theta g := by
    funext k
    cases k with
    | zero => rw [Theta_wall, Theta_wall]
    | succ k => exact h (k + 1) (by omega)
  funext s
  rw [← Theta_free f s, ← Theta_free g s, hfg]

/-- `X c k t` depends only on `c t, …, c (t+k-1)`. -/
theorem X_dep (k : Nat) : ∀ (c c' : Nat → Bool) (t : Nat),
    (∀ i, t ≤ i → i < t + k → c i = c' i) → X c k t = X c' k t := by
  have key : ∀ k, (∀ (c c' : Nat → Bool) (t : Nat), (∀ i, t ≤ i → i < t + k → c i = c' i) →
        X c k t = X c' k t) ∧
      (∀ (c c' : Nat → Bool) (t : Nat), (∀ i, t ≤ i → i < t + (k + 1) → c i = c' i) →
        X c (k + 1) t = X c' (k + 1) t) := by
    intro k
    induction k with
    | zero =>
      refine ⟨fun c c' t _ => by rw [X_zero, X_zero], fun c c' t h => ?_⟩
      rw [X_one, X_one]; exact h t (by omega) (by omega)
    | succ k ih =>
      refine ⟨ih.2, fun c c' t h => ?_⟩
      show X c (k + 2) t = X c' (k + 2) t
      rw [X_add_two, X_add_two,
        ih.2 c c' (t + 1) (fun i h1 h2 => h i (by omega) (by omega)),
        ih.2 c c' t (fun i h1 h2 => h i (by omega) (by omega)),
        ih.1 c c' t (fun i h1 h2 => h i (by omega) (by omega))]
  exact (key k).1

/-- Affine dependence on the last entry: `X c (k+1) t = c (t+k) xor G(c t, …, c (t+k-1))`. -/
theorem X_aff (k : Nat) : ∀ (c c' : Nat → Bool) (t : Nat),
    (∀ i, t ≤ i → i < t + k → c i = c' i) →
    xor (X c (k + 1) t) (X c' (k + 1) t) = xor (c (t + k)) (c' (t + k)) := by
  induction k with
  | zero => intro c c' t _; rw [X_one, X_one]; rfl
  | succ k ih =>
    intro c c' t h
    show xor (X c (k + 2) t) (X c' (k + 2) t) = xor (c (t + (k + 1))) (c' (t + (k + 1)))
    rw [X_add_two, X_add_two,
      X_dep (k + 1) c c' t (fun i h1 h2 => h i h1 (by omega)),
      X_dep k c c' t (fun i h1 h2 => h i h1 (by omega))]
    have key := ih c c' (t + 1) (fun i h1 h2 => h i (by omega) (by omega))
    rw [show t + (k + 1) = t + 1 + k by omega, ← key]
    generalize X c (k + 1) (t + 1) = a
    generalize X c' (k + 1) (t + 1) = b
    generalize (X c' (k + 1) t || X c' k t) = d
    cases a <;> cases b <;> cases d <;> rfl

/-- Continuity of `Theta`: `Theta f k` depends only on the `f s` with `2 s + 2 ≤ k`. -/
theorem Theta_dep (f g : Nat → Bool) (k : Nat) (h : ∀ s, 2 * s + 2 ≤ k → f s = g s) :
    Theta f k = Theta g k := by
  unfold Theta
  apply X_dep k (col f) (col g) 0
  intro i _ hi
  unfold col
  by_cases hi2 : i % 2 = 0
  · rw [if_pos hi2, if_pos hi2]
  · rw [if_neg hi2, if_neg hi2]; exact h (i / 2) (by omega)

/-- Continuity of the inverse on the image: `f s` is determined by `Theta f 0, …, Theta f (2s+2)`. -/
theorem inverse_dep (f g : Nat → Bool) (s : Nat)
    (h : ∀ k, k ≤ 2 * s + 2 → Theta f k = Theta g k) : f s = g s := by
  rw [← Theta_free f s, ← Theta_free g s]
  exact run_dep (2 * s + 1) (Theta f) (Theta g) 1 (fun i hi => h i (by omega))

/-- Triangular form, odd depths: `Theta f (2j+1) = h_j(f 0, …, f (j-1))`. -/
theorem tri_odd (f g : Nat → Bool) (j : Nat) (h : ∀ s, s < j → f s = g s) :
    Theta f (2 * j + 1) = Theta g (2 * j + 1) :=
  Theta_dep f g (2 * j + 1) (fun s hs => h s (by omega))

/-- Triangular form, even depths: given `f 0, …, f (j-1)`, `Theta f (2j+2)` flips exactly with `f j`. -/
theorem tri_even (f g : Nat → Bool) (j : Nat) (h : ∀ s, s < j → f s = g s) :
    xor (Theta f (2 * j + 2)) (Theta g (2 * j + 2)) = xor (f j) (g j) := by
  unfold Theta
  show xor (X (col f) (2 * j + 1 + 1) 0) (X (col g) (2 * j + 1 + 1) 0) = xor (f j) (g j)
  rw [X_aff (2 * j + 1) (col f) (col g) 0 (by
    intro i _ h2
    unfold col
    by_cases hi2 : i % 2 = 0
    · rw [if_pos hi2, if_pos hi2]
    · rw [if_neg hi2, if_neg hi2]; exact h (i / 2) (by omega))]
  unfold col
  rw [if_neg (by omega), if_neg (by omega), show (0 + (2 * j + 1)) / 2 = j by omega]

theorem bool_lemma1 : ∀ A B a b : Bool, xor A B = xor a b → xor A (!a) = xor B (!b) := by decide
theorem bool_lemma2 : ∀ A a : Bool, A = xor (!a) (xor A (!a)) := by decide

/-- The claim's exact shape: `Theta f (2j) = (not f_{j-1}) xor g_j(f_0..f_{j-2})` for `j ≥ 1`
(stated here with `j+1` in place of `j`). -/
theorem tri_even_form (j : Nat) : ∃ G : (Nat → Bool) → Bool,
    (∀ f g, (∀ s, s < j → f s = g s) → G f = G g) ∧
    ∀ f, Theta f (2 * j + 2) = xor (!f j) (G f) := by
  refine ⟨fun f => xor (Theta f (2 * j + 2)) (!f j), ?_, ?_⟩
  · intro f g h
    exact bool_lemma1 _ _ _ _ (tri_even f g j h)
  · intro f
    exact bool_lemma2 _ _

theorem tri_odd_form (j : Nat) : ∃ H : (Nat → Bool) → Bool,
    (∀ f g, (∀ s, s < j → f s = g s) → H f = H g) ∧ ∀ f, Theta f (2 * j + 1) = H f :=
  ⟨fun f => Theta f (2 * j + 1), fun f g h => tri_odd f g j h, fun _ => rfl⟩

/-- Equivariance `Z² ∘ Theta = Theta ∘ σ`. -/
theorem equivariance (f : Nat → Bool) : step (step (Theta f)) = Theta (shift f) := by
  have hy0 : run (Theta f) 2 0 = false := rfl
  have hc : Constrained0 (run (Theta f) 2) := by
    intro s
    rw [← run_add, show 2 + 2 * s = 2 * (s + 1) by omega]
    exact Theta_constrained f (s + 1)
  have key := a_forward (run (Theta f) 2) hy0 hc
  have hf : (fun s => run (run (Theta f) 2) (2 * s + 1) 1) = shift f := by
    funext s
    rw [← run_add, show 2 + (2 * s + 1) = 2 * (s + 1) + 1 by omega, Theta_free]
    rfl
  rw [hf] at key
  exact key

/-- The image `S` is closed: a wall-respecting row all of whose finite windows are windows of
elements of `S` lies in `S`. -/
theorem S_closed (x : Nat → Bool) (hw : x 0 = false)
    (h : ∀ n, ∃ f, ∀ k, k ≤ n → x k = Theta f k) : ∃ f, x = Theta f := by
  refine ⟨_, a_forward x hw ?_⟩
  intro s
  obtain ⟨f, hf⟩ := h (2 * s + 1)
  rw [run_dep (2 * s) x (Theta f) 1 (fun i hi => hf i (by omega))]
  exact Theta_constrained f s

/-! ## Part (c) -/

def FiniteW (x : Nat → Bool) (W : Nat) : Prop := ∀ k, W < k → x k = false

theorem finite_step (x : Nat → Bool) (W : Nat) (hx : FiniteW x W) : FiniteW (step x) (W + 1) := by
  intro k hk
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [step_succ, hx (j + 2) (by omega), hx (j + 1) (by omega), hx j (by omega)]
  rfl

theorem finite_run (x : Nat → Bool) (W : Nat) (hx : FiniteW x W) (t : Nat) :
    FiniteW (run x t) (W + t) := by
  induction t with
  | zero => exact hx
  | succ t ih => rw [run_succ, ← Nat.add_assoc]; exact finite_step _ _ ih

/-- Q_01 in its most general reading: no finitely supported wall-respecting start keeps column 1
black at every other step from some time `T` on (either phase). -/
def Q01 : Prop := ∀ (x : Nat → Bool) (W T : Nat), x 0 = false → FiniteW x W →
  ¬ ∀ s, run x (T + 2 * s) 1 = true

/-- **Part (c), first sentence.** -/
theorem part_c1 : Q01 ↔ ∀ f W, ¬ FiniteW (Theta f) W := by
  constructor
  · intro hQ f W hfin
    apply hQ (Theta f) W 0 (Theta_wall f) hfin
    intro s; rw [Nat.zero_add]; exact Theta_constrained f s
  · intro hN x W T hw hfin hcon
    have hy : Constrained0 (run x T) := by
      intro s; rw [← run_add]; exact hcon s
    have key := a_forward (run x T) (run_wall hw T) hy
    apply hN (fun s => run (run x T) (2 * s + 1) 1) (W + T)
    rw [← key]
    exact finite_run x W hfin T

/-- `F_W = {f | Theta f has width ≤ W}` is closed in the product topology: a point all of whose
finite prefixes extend to members of `F_W` lies in `F_W`. -/
theorem FW_closed (W : Nat) (f : Nat → Bool)
    (h : ∀ n, ∃ g, (∀ s, s < n → g s = f s) ∧ ∀ k, W < k → Theta g k = false) :
    ∀ k, W < k → Theta f k = false := by
  intro k hk
  obtain ⟨g, hgf, hg⟩ := h k
  rw [← Theta_dep g f k (fun s hs => hgf s (by omega))]
  exact hg k hk

/-- Depth `d` of the search tree for width `W`: the prefix `f 0, …, f (d-1)` keeps depths `W+1 … 2d+1`
white (these depths are determined by that prefix, see `level_prefix`). -/
def Level (W d : Nat) (f : Nat → Bool) : Prop := ∀ k, W < k → k ≤ 2 * d + 1 → Theta f k = false

theorem level_prefix (W d : Nat) (f g : Nat → Bool) (h : ∀ s, s < d → f s = g s) :
    Level W d f → Level W d g := by
  intro hf k h1 h2
  rw [← Theta_dep f g k (fun s hs => h s (by omega))]
  exact hf k h1 h2

def Good (W n : Nat) (g : Nat → Bool) : Prop :=
  ∀ d, ∃ f, (∀ i, i < n → f i = g i) ∧ Level W d f

def ext (g : Nat → Bool) (n : Nat) (b : Bool) : Nat → Bool := fun i => if i = n then b else g i

theorem good_ext (W n : Nat) (g : Nat → Bool) (hg : Good W n g) :
    Good W (n + 1) (ext g n false) ∨ Good W (n + 1) (ext g n true) := by
  apply Classical.byContradiction
  intro hneg
  have hA : ¬ Good W (n + 1) (ext g n false) := fun h => hneg (Or.inl h)
  have hB : ¬ Good W (n + 1) (ext g n true) := fun h => hneg (Or.inr h)
  obtain ⟨d0, hd0⟩ := Classical.not_forall.mp hA
  obtain ⟨d1, hd1⟩ := Classical.not_forall.mp hB
  obtain ⟨f, hfg, hf⟩ := hg (max d0 d1)
  have hm0 := Nat.le_max_left d0 d1
  have hm1 := Nat.le_max_right d0 d1
  have hpre : ∀ i, i < n + 1 → f i = ext g n (f n) i := by
    intro i hi
    unfold ext
    by_cases hin : i = n
    · rw [if_pos hin, hin]
    · rw [if_neg hin]; exact hfg i (by omega)
  cases hfn : f n with
  | false =>
    rw [hfn] at hpre
    exact hd0 ⟨f, hpre, fun k h1 h2 => hf k h1 (by omega)⟩
  | true =>
    rw [hfn] at hpre
    exact hd1 ⟨f, hpre, fun k h1 h2 => hf k h1 (by omega)⟩

open Classical in
noncomputable def choiceBit (W n : Nat) (g : Nat → Bool) : Bool :=
  if Good W (n + 1) (ext g n false) then false else true

theorem good_choice (W n : Nat) (g : Nat → Bool) (hg : Good W n g) :
    Good W (n + 1) (ext g n (choiceBit W n g)) := by
  unfold choiceBit
  by_cases hc : Good W (n + 1) (ext g n false)
  · rw [if_pos hc]; exact hc
  · rw [if_neg hc]; exact (good_ext W n g hg).resolve_left hc

noncomputable def branch (W : Nat) : Nat → (Nat → Bool)
  | 0 => fun _ => false
  | n + 1 => ext (branch W n) n (choiceBit W n (branch W n))

theorem branch_good (W : Nat) (h0 : ∀ d, ∃ f, Level W d f) : ∀ n, Good W n (branch W n) := by
  intro n
  induction n with
  | zero =>
    intro d
    obtain ⟨f, hf⟩ := h0 d
    exact ⟨f, fun i hi => absurd hi (Nat.not_lt_zero _), hf⟩
  | succ n ih => exact good_choice W n (branch W n) ih

theorem branch_stable (W i : Nat) : ∀ m, i < m → branch W m i = branch W (i + 1) i := by
  intro m
  induction m with
  | zero => intro hm; exact absurd hm (Nat.not_lt_zero _)
  | succ m ih =>
    intro hm
    by_cases him : i = m
    · subst him; rfl
    · show ext (branch W m) m (choiceBit W m (branch W m)) i = _
      unfold ext
      rw [if_neg him]
      exact ih (by omega)

noncomputable def limitF (W : Nat) : Nat → Bool := fun i => branch W (i + 1) i

/-- **Part (c), second sentence** (König / compactness): `F_W` is nonempty iff every finite depth of
the search tree is nonempty. -/
theorem koenig (W : Nat) :
    (∃ f, ∀ k, W < k → Theta f k = false) ↔ ∀ d, ∃ f, Level W d f := by
  constructor
  · rintro ⟨f, hf⟩ d; exact ⟨f, fun k h1 _ => hf k h1⟩
  · intro h0
    refine ⟨limitF W, fun k hk => ?_⟩
    obtain ⟨f, hpre, hf⟩ := branch_good W h0 k k
    have heq : Theta (limitF W) k = Theta f k := by
      apply Theta_dep
      intro s hs
      rw [hpre s (by omega)]
      exact (branch_stable W s k (by omega)).symm
    rw [heq]
    exact hf k hk (by omega)

/-! ## Part (d) -/

/-- The row of width `≤ l.length` with `L(k) = l[k-1]` for `1 ≤ k ≤ l.length`. -/
def toRow (l : List Bool) (k : Nat) : Bool := if k = 0 then false else (l[k - 1]?).getD false

/-- Constraint at every even time `t ≤ |l| - 1`. -/
def ok (l : List Bool) : Prop := ∀ t, t < l.length → t % 2 = 0 → run (toRow l) t 1 = true

instance (l : List Bool) : Decidable (ok l) := by unfold ok; infer_instance

/-- `cnt n l` = number of Boolean extensions `e` of length `n` with `ok (l ++ e)`. -/
def cnt : Nat → List Bool → Nat
  | 0, l => if ok l then 1 else 0
  | n + 1, l => cnt n (l ++ [false]) + cnt n (l ++ [true])

theorem toRow_wall (l : List Bool) : toRow l 0 = false := rfl

theorem toRow_finite (l : List Bool) : FiniteW (toRow l) l.length := by
  intro k hk
  unfold toRow
  rw [if_neg (by omega), List.getElem?_eq_none (by omega)]
  rfl

theorem toRow_snoc_le (l : List Bool) (b : Bool) (i : Nat) (hi : i ≤ l.length) :
    toRow (l ++ [b]) i = toRow l i := by
  unfold toRow
  by_cases h0 : i = 0
  · rw [if_pos h0, if_pos h0]
  · rw [if_neg h0, if_neg h0, List.getElem?_append_left (by omega)]

theorem toRow_snoc_last (l : List Bool) (b : Bool) :
    toRow (l ++ [b]) (l.length + 1) = b := by
  unfold toRow
  rw [if_neg (by omega), show l.length + 1 - 1 = l.length by omega,
    List.getElem?_append_right (by omega)]
  simp

theorem ok_snoc (l : List Bool) (b : Bool) :
    ok (l ++ [b]) ↔ ok l ∧ (l.length % 2 = 0 → run (toRow (l ++ [b])) l.length 1 = true) := by
  have hagree : ∀ t, t < l.length → run (toRow (l ++ [b])) t 1 = run (toRow l) t 1 := by
    intro t ht
    exact run_dep t _ _ 1 (fun i hi => toRow_snoc_le l b i (by omega))
  have hlen : (l ++ [b]).length = l.length + 1 := by simp
  constructor
  · intro h
    refine ⟨fun t ht he => ?_, fun he => h l.length (by omega) he⟩
    rw [← hagree t ht]; exact h t (by omega) he
  · rintro ⟨h1, h2⟩ t ht he
    by_cases htl : t < l.length
    · rw [hagree t htl]; exact h1 t htl he
    · have : t = l.length := by omega
      subst this; exact h2 he

theorem ok_of_snoc (l : List Bool) (b : Bool) (h : ok (l ++ [b])) : ok l := ((ok_snoc l b).mp h).1

/-- The pivot: the constraint at time `|l|` flips exactly with the appended bit `L(|l|+1)`. -/
theorem pivot (l : List Bool) :
    run (toRow (l ++ [true])) l.length 1 = !(run (toRow (l ++ [false])) l.length 1) := by
  have key := run_aff l.length (toRow (l ++ [true])) (toRow (l ++ [false])) 1 (Nat.le_refl 1)
    (fun i hi => by rw [toRow_snoc_le l true i (by omega), toRow_snoc_le l false i (by omega)])
  rw [show 1 + l.length = l.length + 1 by omega, toRow_snoc_last, toRow_snoc_last] at key
  revert key
  generalize run (toRow (l ++ [true])) l.length 1 = A
  generalize run (toRow (l ++ [false])) l.length 1 = B
  cases A <;> cases B <;> decide

theorem cnt_eq (n : Nat) : ∀ l : List Bool,
    cnt n l = if ok l then 2 ^ ((l.length + n) / 2 - l.length / 2) else 0 := by
  induction n with
  | zero =>
    intro l
    rw [cnt, Nat.add_zero, Nat.sub_self, Nat.pow_zero]
  | succ n ih =>
    intro l
    rw [cnt, ih (l ++ [false]), ih (l ++ [true])]
    have hlen0 : (l ++ [false]).length = l.length + 1 := by simp
    have hlen1 : (l ++ [true]).length = l.length + 1 := by simp
    rw [hlen0, hlen1]
    by_cases hl : ok l
    · rw [if_pos hl]
      by_cases hm : l.length % 2 = 0
      · have e0 := ok_snoc l false
        have e1 := ok_snoc l true
        have hp := pivot l
        by_cases hb : run (toRow (l ++ [false])) l.length 1 = true
        · have h0 : ok (l ++ [false]) := e0.mpr ⟨hl, fun _ => hb⟩
          have h1 : ¬ ok (l ++ [true]) := by
            intro h
            have := (e1.mp h).2 hm
            rw [hp, hb] at this
            exact absurd this (by decide)
          rw [if_pos h0, if_neg h1, Nat.add_zero]
          congr 1; omega
        · have h0 : ¬ ok (l ++ [false]) := by
            intro h; exact hb ((e0.mp h).2 hm)
          have hb' : run (toRow (l ++ [false])) l.length 1 = false := by
            revert hb; generalize run (toRow (l ++ [false])) l.length 1 = B; cases B <;> decide
          have h1 : ok (l ++ [true]) := by
            refine e1.mpr ⟨hl, fun _ => ?_⟩
            rw [hp, hb']; rfl
          rw [if_neg h0, if_pos h1, Nat.zero_add]
          congr 1; omega
      · have h0 : ok (l ++ [false]) := (ok_snoc l false).mpr ⟨hl, fun h => absurd h hm⟩
        have h1 : ok (l ++ [true]) := (ok_snoc l true).mpr ⟨hl, fun h => absurd h hm⟩
        rw [if_pos h0, if_pos h1, ← Nat.two_mul, ← Nat.pow_succ']
        congr 1; omega
    · rw [if_neg hl]
      have h0 : ¬ ok (l ++ [false]) := fun h => hl (ok_of_snoc l false h)
      have h1 : ¬ ok (l ++ [true]) := fun h => hl (ok_of_snoc l true h)
      rw [if_neg h0, if_neg h1]

/-- **Part (d).** Exactly `2 ^ ⌊W/2⌋` rows of width `≤ W` satisfy the constraint at every even time
`t ≤ W - 1`. -/
theorem part_d (W : Nat) : cnt W [] = 2 ^ (W / 2) := by
  rw [cnt_eq]
  have h : ok [] := fun t ht => absurd ht (Nat.not_lt_zero _)
  rw [if_pos h]
  show 2 ^ ((0 + W) / 2 - 0 / 2) = 2 ^ (W / 2)
  congr 1; omega

/-- Every wall-respecting row of width `≤ W` is `toRow l` for a list of length `W` (so `cnt W []`
counts exactly the rows of width `≤ W`). -/
theorem row_is_list (x : Nat → Bool) (W : Nat) (hw : x 0 = false) (hx : FiniteW x W) :
    ∃ l : List Bool, l.length = W ∧ toRow l = x := by
  refine ⟨(List.range W).map (fun i => x (i + 1)), by simp, ?_⟩
  funext k
  unfold toRow
  by_cases hk : k = 0
  · rw [if_pos hk, hk, hw]
  · rw [if_neg hk]
    by_cases hkW : k ≤ W
    · rw [List.getElem?_map, List.getElem?_range (by omega)]
      show x (k - 1 + 1) = x k
      rw [show k - 1 + 1 = k by omega]
    · rw [List.getElem?_eq_none (by simp; omega), hx k (by omega)]
      rfl

theorem toRow_inj (l l' : List Bool) (hlen : l.length = l'.length) (h : toRow l = toRow l') : l = l' := by
  apply List.ext_getElem?
  intro i
  have := congrFun h (i + 1)
  unfold toRow at this
  rw [if_neg (by omega), if_neg (by omega), show i + 1 - 1 = i by omega] at this
  by_cases hi : i < l.length
  · rw [List.getElem?_eq_getElem hi, List.getElem?_eq_getElem (by omega)] at this ⊢
    simp at this
    rw [this]
  · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]

end A1ReformCheck

open A1ReformCheck in
#print axioms part_a
open A1ReformCheck in
#print axioms Theta_inj
open A1ReformCheck in
#print axioms tri_even_form
open A1ReformCheck in
#print axioms tri_odd_form
open A1ReformCheck in
#print axioms equivariance
open A1ReformCheck in
#print axioms S_closed
open A1ReformCheck in
#print axioms inverse_dep
open A1ReformCheck in
#print axioms part_c1
open A1ReformCheck in
#print axioms koenig
open A1ReformCheck in
#print axioms FW_closed
open A1ReformCheck in
#print axioms part_d
open A1ReformCheck in
#print axioms row_is_list
open A1ReformCheck in
#print axioms toRow_inj

#eval (List.range 15).map (fun W => A1ReformCheck.cnt W [])

-- writeup-r2 axiom audit (appended)
#print axioms A1ReformCheck.part_a
#print axioms A1ReformCheck.Theta_inj
#print axioms A1ReformCheck.tri_even_form
#print axioms A1ReformCheck.tri_odd_form
#print axioms A1ReformCheck.equivariance
#print axioms A1ReformCheck.S_closed
#print axioms A1ReformCheck.inverse_dep
#print axioms A1ReformCheck.part_c1
#print axioms A1ReformCheck.FW_closed
#print axioms A1ReformCheck.koenig
#print axioms A1ReformCheck.part_d
#print axioms A1ReformCheck.row_is_list
#print axioms A1ReformCheck.toRow_inj
