namespace R30ZBLsa
/-- Rule 30 on the half-line `k ≥ 1` with the cell at `k = 0` held white.
`zrow L t k` is the colour at time `t` and position `k` (standing for cell `-k`); `L` is the
initial row, whose value at `0` is ignored. -/
def zrow (L : Nat → Bool) : Nat → Nat → Bool
  | 0, k => if k = 0 then false else L k
  | t + 1, k => if k = 0 then false else xor (zrow L t (k + 1)) (zrow L t k || zrow L t (k - 1))

theorem zrow_zero_pos (L : Nat → Bool) : ∀ t, zrow L t 0 = false
  | 0 => rfl
  | _ + 1 => rfl

theorem zrow_init (L : Nat → Bool) (k : Nat) : zrow L 0 (k + 1) = L (k + 1) := rfl

theorem zrow_succ (L : Nat → Bool) (t k : Nat) :
    zrow L (t + 1) (k + 1) = xor (zrow L t (k + 2)) (zrow L t (k + 1) || zrow L t k) := rfl

/-- Left-permutive inversion inside the ZBL. -/
theorem zrow_inv (L : Nat → Bool) (t k : Nat) :
    zrow L t (k + 2) = xor (zrow L (t + 1) (k + 1)) (zrow L t (k + 1) || zrow L t k) := by
  rw [zrow_succ]; cases zrow L t (k + 2) <;> cases (zrow L t (k + 1) || zrow L t k) <;> rfl

/-- Shift in time: the ZBL is a semiflow. -/
theorem zrow_shift (L : Nat → Bool) (s : Nat) : ∀ t k, zrow L (s + t) k = zrow (zrow L s) t k := by
  intro t
  induction t with
  | zero =>
    intro k
    cases k with
    | zero => simp [zrow_zero_pos]
    | succ k => rfl
  | succ t ih =>
    intro k
    cases k with
    | zero => simp [zrow_zero_pos]
    | succ k =>
      rw [show s + (t + 1) = (s + t) + 1 by omega, zrow_succ, zrow_succ, ih, ih, ih]
/-- Constrained rows: column `1` of the ZBL is black at all even times. -/
def InX (L : Nat → Bool) : Prop := ∀ s, zrow L (2 * s) 1 = true

/-- Finitely supported rows. -/
def FinSupp (L : Nat → Bool) : Prop := ∃ W, ∀ k, W < k → L k = false

/-- **Q01**: no finitely supported row is constrained. -/
def Q01 : Prop := ∀ L : Nat → Bool, FinSupp L → ¬ InX L
/-! ## The reconstruction map: the boundary column determines the row -/

/-- **Trace determination.** Position `k` at time `t` depends only on the boundary column at times
`t, …, t + k - 1`. -/
theorem zrow_det (L L' : Nat → Bool) :
    ∀ k t, (∀ i, i < k → zrow L (t + i) 1 = zrow L' (t + i) 1) → zrow L t k = zrow L' t k := by
  have key : ∀ k, (∀ t, (∀ i, i < k → zrow L (t + i) 1 = zrow L' (t + i) 1) →
      zrow L t k = zrow L' t k) ∧
      (∀ t, (∀ i, i < k + 1 → zrow L (t + i) 1 = zrow L' (t + i) 1) →
      zrow L t (k + 1) = zrow L' t (k + 1)) := by
    intro k
    induction k with
    | zero =>
      refine ⟨fun t _ => by rw [zrow_zero_pos, zrow_zero_pos], fun t h => ?_⟩
      have := h 0 (by omega)
      simpa using this
    | succ k ih =>
      refine ⟨ih.2, fun t h => ?_⟩
      rw [zrow_inv L t k, zrow_inv L' t k]
      have e1 : zrow L (t + 1) (k + 1) = zrow L' (t + 1) (k + 1) :=
        ih.2 (t + 1) fun i hi => by
          have := h (i + 1) (by omega)
          rwa [show t + (i + 1) = t + 1 + i by omega] at this
      have e2 : zrow L t (k + 1) = zrow L' t (k + 1) := ih.2 t fun i hi => h i (by omega)
      have e3 : zrow L t k = zrow L' t k := ih.1 t fun i hi => h i (by omega)
      rw [e1, e2, e3]
  exact fun k => (key k).1

/-- **Pivot structure.** If the boundary columns agree at times `t, …, t + k - 1`, then the rows at
time `t` differ at position `k + 1` exactly when the boundary columns differ at time `t + k`.
In particular the initial row `L(k + 1)` is the boundary value `y_k` xor a function of `y_0..y_{k-1}`. -/
theorem zrow_pivot (L L' : Nat → Bool) :
    ∀ k t, (∀ i, i < k → zrow L (t + i) 1 = zrow L' (t + i) 1) →
      xor (zrow L t (k + 1)) (zrow L' t (k + 1)) = xor (zrow L (t + k) 1) (zrow L' (t + k) 1) := by
  intro k
  induction k with
  | zero => intro t _; rfl
  | succ k ih =>
    intro t h
    rw [zrow_inv L t k, zrow_inv L' t k]
    have e2 : zrow L t (k + 1) = zrow L' t (k + 1) := zrow_det L L' (k + 1) t fun i hi => h i hi
    have e3 : zrow L t k = zrow L' t k := zrow_det L L' k t fun i hi => h i (by omega)
    have := ih (t + 1) fun i hi => by
      have := h (i + 1) (by omega)
      rwa [show t + (i + 1) = t + 1 + i by omega] at this
    rw [e2, e3, show t + (k + 1) = t + 1 + k by omega, ← this]
    cases zrow L (t + 1) (k + 1) <;> cases zrow L' (t + 1) (k + 1) <;>
      cases (zrow L' t (k + 1) || zrow L' t k) <;> rfl

/-- The spatial (left-permutive) reconstruction from a boundary column `y`:
`recon y k t` is the colour at position `k`, time `t`. -/
def recon (y : Nat → Bool) : Nat → Nat → Bool
  | 0, _ => false
  | 1, t => y t
  | k + 2, t => xor (recon y (k + 1) (t + 1)) (recon y (k + 1) t || recon y k t)

theorem zrow_recon (y : Nat → Bool) : ∀ t k, zrow (fun k => recon y k 0) t k = recon y k t := by
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
    | succ k =>
      rw [zrow_succ, ih, ih, ih]
      show _ = recon y (k + 1) (t + 1)
      have hdef : recon y (k + 2) t =
          xor (recon y (k + 1) (t + 1)) (recon y (k + 1) t || recon y k t) := by
        cases k <;> rfl
      rw [hdef]
      cases recon y (k + 1) (t + 1) <;> cases (recon y (k + 1) t || recon y k t) <;> rfl

/-- **The trace map is onto**: every boundary column is the boundary column of some row (and of only
one, by `zrow_det`). So the constrained rows are in bijection with the free-bit sequences `f`. -/
theorem trace_surj (y : Nat → Bool) : ∃ L : Nat → Bool, ∀ t, zrow L t 1 = y t :=
  ⟨fun k => recon y k 0, fun t => zrow_recon y t 1⟩

/-- The reconstruction map `Φ`: free bits `f` ↦ the unique constrained row with
`zrow L (2s+1) 1 = f s`. -/
def Phi (f : Nat → Bool) : Nat → Bool :=
  fun k => recon (fun t => if t % 2 = 0 then true else f (t / 2)) k 0

theorem Phi_inX (f : Nat → Bool) : InX (Phi f) := by
  intro s
  show zrow (fun k => recon (fun t => if t % 2 = 0 then true else f (t / 2)) k 0) (2 * s) 1 = true
  rw [zrow_recon]
  show (if 2 * s % 2 = 0 then true else f (2 * s / 2)) = true
  rw [if_pos (by omega)]

theorem Phi_free (f : Nat → Bool) (s : Nat) : zrow (Phi f) (2 * s + 1) 1 = f s := by
  show zrow (fun k => recon (fun t => if t % 2 = 0 then true else f (t / 2)) k 0) (2 * s + 1) 1 = f s
  rw [zrow_recon]
  show (if (2 * s + 1) % 2 = 0 then true else f ((2 * s + 1) / 2)) = f s
  rw [if_neg (by omega), show (2 * s + 1) / 2 = s by omega]

/-- `Q01` restated through `Φ`: no free-bit sequence gives a finitely supported row. -/
theorem Q01_iff_Phi : Q01 ↔ ∀ f, ¬ FinSupp (Phi f) := by
  constructor
  · intro hQ f hfin
    exact hQ _ hfin (Phi_inX f)
  · intro h L hfin hX
    let f : Nat → Bool := fun s => zrow L (2 * s + 1) 1
    have htr : ∀ k, (∀ i, i < k → zrow L (0 + i) 1 = zrow (Phi f) (0 + i) 1) := by
      intro k i _
      rw [Nat.zero_add]
      obtain ⟨s, hs⟩ : ∃ s, i = 2 * s ∨ i = 2 * s + 1 := ⟨i / 2, by omega⟩
      rcases hs with rfl | rfl
      · rw [hX s, Phi_inX f s]
      · rw [Phi_free f s]
    apply h f
    obtain ⟨W, hW⟩ := hfin
    refine ⟨W, fun k hk => ?_⟩
    have e := zrow_det L (Phi f) k 0 (htr k)
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    have e1 : zrow L 0 (k' + 1) = L (k' + 1) := rfl
    have e2 : zrow (Phi f) 0 (k' + 1) = Phi f (k' + 1) := rfl
    rw [← e2, ← e, e1]
    exact hW _ hk

/-! ## Verifier additions (not part of the original file) -/

/-- (c) uniqueness: a constrained row with free bits `f` equals `Phi f` at every position `k ≥ 1`
(position `0` is ignored by `zrow`). -/
theorem V_Phi_unique (L f : Nat → Bool) (hX : InX L)
    (hf : ∀ s, zrow L (2 * s + 1) 1 = f s) : ∀ k, 1 ≤ k → L k = Phi f k := by
  intro k hk
  have htr : ∀ i, i < k → zrow L (0 + i) 1 = zrow (Phi f) (0 + i) 1 := by
    intro i _
    rw [Nat.zero_add]
    obtain ⟨s, hs⟩ : ∃ s, i = 2 * s ∨ i = 2 * s + 1 := ⟨i / 2, by omega⟩
    rcases hs with rfl | rfl
    · rw [hX s, Phi_inX f s]
    · rw [hf s, Phi_free f s]
  have e := zrow_det L (Phi f) k 0 htr
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  exact e

/-- Boundary columns of `Phi f` and `Phi f'` agree below `n` when the free bits agree below
`(n) / 2` (free bit `f_j` sits at time `2j+1`). -/
theorem V_Phi_trace_agree (f f' : Nat → Bool) (n : Nat)
    (h : ∀ j, 2 * j + 1 < n → f j = f' j) :
    ∀ i, i < n → zrow (Phi f) (0 + i) 1 = zrow (Phi f') (0 + i) 1 := by
  intro i hi
  rw [Nat.zero_add]
  obtain ⟨j, hj⟩ : ∃ j, i = 2 * j ∨ i = 2 * j + 1 := ⟨i / 2, by omega⟩
  rcases hj with rfl | rfl
  · rw [Phi_inX f j, Phi_inX f' j]
  · rw [Phi_free f j, Phi_free f' j]; exact h j hi

/-- (d), first half: `L(2s+2) = f_s xor g_s(f_<s)`, with `g_s` depending only on `f_0..f_{s-1}`. -/
theorem V_d_even : ∃ g : Nat → (Nat → Bool) → Bool,
    (∀ s f f', (∀ i, i < s → f i = f' i) → g s f = g s f') ∧
    (∀ f s, Phi f (2 * s + 2) = xor (f s) (g s f)) := by
  refine ⟨fun s f => xor (Phi f (2 * s + 2)) (f s), ?_, ?_⟩
  · intro s f f' h
    have hy := V_Phi_trace_agree f f' (2 * s + 1) (fun j hj => h j (by omega))
    have p := zrow_pivot (Phi f) (Phi f') (2 * s + 1) 0 hy
    rw [Nat.zero_add, Phi_free, Phi_free] at p
    have e1 : zrow (Phi f) 0 (2 * s + 1 + 1) = Phi f (2 * s + 2) := rfl
    have e2 : zrow (Phi f') 0 (2 * s + 1 + 1) = Phi f' (2 * s + 2) := rfl
    rw [e1, e2] at p
    show xor (Phi f (2 * s + 2)) (f s) = xor (Phi f' (2 * s + 2)) (f' s)
    revert p
    cases Phi f (2 * s + 2) <;> cases Phi f' (2 * s + 2) <;> cases f s <;> cases f' s <;> decide
  · intro f s
    show Phi f (2 * s + 2) = xor (f s) (xor (Phi f (2 * s + 2)) (f s))
    cases Phi f (2 * s + 2) <;> cases f s <;> rfl

/-- (d), second half: `L(2s+3) = h_s(f_0..f_s)` (no dependence on `f_{s+1}, …`). -/
theorem V_d_odd (f f' : Nat → Bool) (s : Nat) (h : ∀ i, i ≤ s → f i = f' i) :
    Phi f (2 * s + 3) = Phi f' (2 * s + 3) :=
  zrow_det (Phi f) (Phi f') (2 * s + 3) 0
    (V_Phi_trace_agree f f' (2 * s + 3) (fun j hj => h j (by omega)))

/-- (d), sharpness of the pivot: flipping only `f_s` flips `L(2s+2)`. -/
theorem V_d_pivot_flip (f f' : Nat → Bool) (s : Nat) (h : ∀ i, i < s → f i = f' i)
    (hs : f s ≠ f' s) : Phi f (2 * s + 2) ≠ Phi f' (2 * s + 2) := by
  obtain ⟨g, hg, hPhi⟩ := V_d_even
  rw [hPhi f s, hPhi f' s, hg s f f' h]
  intro he
  apply hs
  revert he
  cases f s <;> cases f' s <;> cases g s f' <;> decide

/-- The ZBL one-step map on rows. -/
def V_F (L : Nat → Bool) : Nat → Bool := zrow L 1

/-- (f): `F² ∘ Φ = Φ ∘ shift`, as an equality of functions `Nat → Bool` (position `0` included). -/
theorem V_F2_Phi (f : Nat → Bool) : V_F (V_F (Phi f)) = Phi (fun s => f (s + 1)) := by
  funext k
  show zrow (zrow (Phi f) 1) 1 k = _
  rw [← zrow_shift]
  cases k with
  | zero => rw [zrow_zero_pos]; rfl
  | succ k =>
    have hy : ∀ i, i < k + 1 →
        zrow (zrow (Phi f) 2) (0 + i) 1 = zrow (Phi (fun s => f (s + 1))) (0 + i) 1 := by
      intro i _
      rw [← zrow_shift, Nat.zero_add]
      obtain ⟨j, hj⟩ : ∃ j, i = 2 * j ∨ i = 2 * j + 1 := ⟨i / 2, by omega⟩
      rcases hj with rfl | rfl
      · rw [show 2 + 2 * j = 2 * (j + 1) by omega, Phi_inX f (j + 1), Phi_inX _ j]
      · rw [show 2 + (2 * j + 1) = 2 * (j + 1) + 1 by omega, Phi_free f (j + 1), Phi_free _ j]
    exact zrow_det _ _ (k + 1) 0 hy

/-- Sanity: the recon row really has boundary column `y` (from `trace_surj`), checked on a
concrete `y` by evaluation. -/
example : (List.range 12).map (fun t => zrow (fun k => recon (fun t => t % 3 == 0) k 0) t 1)
    = (List.range 12).map (fun t => t % 3 == 0) := by decide

end R30ZBLsa
#print axioms R30ZBLsa.Q01_iff_Phi
#print axioms R30ZBLsa.V_F2_Phi
#print axioms R30ZBLsa.V_d_even
#print axioms R30ZBLsa.V_Phi_unique
