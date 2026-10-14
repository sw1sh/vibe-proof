import QTilde.Basic

/-!
# Cloitre's two-tape interleaving

Cloitre (arXiv:2604.06237, Definition 2.3): `Interleave(X, Y, ε)` is emitted by a machine that, in
state `false`, reads the next letter of `X`, and in state `true`, the next letter of `Y`. The
emitted letter becomes the next state. The interleaving has *exact fit* (`Fits`) if the machine
never requests an exhausted tape.

We model the machine by its head positions over time (`head`). Under exact fit:

* `pre_count`: every prefix of the output is a shuffle of prefixes of the two tapes, so letter
  counts add (Cloitre's Lemma 2.4 for heights: `pre_ht`).
* `head_i_eq`, `head_j_eq`: the heads are determined by the emitted prefix (Lemma 2.5).
* `fits_of_inv`: a counting criterion for exact fit, used for both of Cloitre's laws (Lemma 2.8).
-/

namespace QTilde

/-- Height of a word: each zero steps up, each one steps down. -/
def ht (w : List Bool) : Int := (w.count false : Int) - (w.count true : Int)

/-- The machine before an output: letters consumed from each tape, and the current state. -/
structure Head where
  i : Nat
  j : Nat
  s : Bool

/-- One step: in state `false` read tape `X`, in state `true` read tape `Y`; the letter read is
emitted and becomes the new state. (An exhausted tape reads `false`; under exact fit this never
happens.) -/
def step (X Y : List Bool) (h : Head) : Head :=
  if h.s then ⟨h.i, h.j + 1, Y.getD h.j false⟩ else ⟨h.i + 1, h.j, X.getD h.i false⟩

/-- The machine after `t` outputs, started in state `ε`. -/
def head (X Y : List Bool) (ε : Bool) : Nat → Head
  | 0 => ⟨0, 0, ε⟩
  | t + 1 => step X Y (head X Y ε t)

/-- The letter emitted at time `t`. -/
def out (X Y : List Bool) (ε : Bool) (t : Nat) : Bool := (head X Y ε (t + 1)).s

/-- The first `t` letters emitted. -/
def pre (X Y : List Bool) (ε : Bool) (t : Nat) : List Bool := (List.range t).map (out X Y ε)

/-- `Interleave(X, Y, ε)`. -/
def interleave (X Y : List Bool) (ε : Bool) : List Bool := pre X Y ε (X.length + Y.length)

/-- Exact fit: the machine never requests an exhausted tape. -/
def Fits (X Y : List Bool) (ε : Bool) : Prop :=
  ∀ t, t < X.length + Y.length →
    ((head X Y ε t).s = false → (head X Y ε t).i < X.length) ∧
    ((head X Y ε t).s = true → (head X Y ε t).j < Y.length)

variable {X Y : List Bool} {ε : Bool}

@[simp] theorem head_zero : head X Y ε 0 = ⟨0, 0, ε⟩ := rfl

theorem head_succ (t : Nat) : head X Y ε (t + 1) = step X Y (head X Y ε t) := rfl

theorem head_i_succ (t : Nat) :
    (head X Y ε (t + 1)).i = (head X Y ε t).i + (if (head X Y ε t).s then 0 else 1) := by
  rw [head_succ, step]; cases (head X Y ε t).s <;> simp

theorem head_j_succ (t : Nat) :
    (head X Y ε (t + 1)).j = (head X Y ε t).j + (if (head X Y ε t).s then 1 else 0) := by
  rw [head_succ, step]; cases (head X Y ε t).s <;> simp

theorem head_s_succ (t : Nat) : (head X Y ε (t + 1)).s = out X Y ε t := rfl

theorem out_eq (t : Nat) :
    out X Y ε t = if (head X Y ε t).s then Y.getD (head X Y ε t).j false
      else X.getD (head X Y ε t).i false := by
  rw [out, head_succ, step]; cases (head X Y ε t).s <;> simp

theorem head_i_add_j (t : Nat) : (head X Y ε t).i + (head X Y ε t).j = t := by
  induction t with
  | zero => rfl
  | succ t ih => rw [head_i_succ, head_j_succ]; cases (head X Y ε t).s <;> simp <;> omega

@[simp] theorem pre_zero : pre X Y ε 0 = [] := rfl

theorem pre_succ (t : Nat) : pre X Y ε (t + 1) = pre X Y ε t ++ [out X Y ε t] := by
  simp [pre, List.range_succ]

@[simp] theorem pre_length (t : Nat) : (pre X Y ε t).length = t := by simp [pre]

@[simp] theorem interleave_length : (interleave X Y ε).length = X.length + Y.length := by
  simp [interleave]

theorem getElem_pre {t u : Nat} (hu : u < (pre X Y ε t).length) :
    (pre X Y ε t)[u] = out X Y ε u := by simp [pre]

theorem pre_take {t u : Nat} (h : u ≤ t) : (pre X Y ε t).take u = pre X Y ε u := by
  simp only [pre, ← List.map_take, List.take_range, Nat.min_eq_left h]

/-- Under exact fit, the letter emitted in state `false` is the next letter of `X`. -/
theorem out_eq_X (hf : Fits X Y ε) {t : Nat} (ht : t < X.length + Y.length)
    (hs : (head X Y ε t).s = false) : out X Y ε t = X[(head X Y ε t).i]'((hf t ht).1 hs) := by
  rw [out_eq, if_neg (by simp [hs])]
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ((hf t ht).1 hs), Option.getD_some]

/-- Under exact fit, the letter emitted in state `true` is the next letter of `Y`. -/
theorem out_eq_Y (hf : Fits X Y ε) {t : Nat} (ht : t < X.length + Y.length)
    (hs : (head X Y ε t).s = true) : out X Y ε t = Y[(head X Y ε t).j]'((hf t ht).2 hs) := by
  rw [out_eq, if_pos hs]
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ((hf t ht).2 hs), Option.getD_some]

/-- Under exact fit, the heads never pass the ends of their tapes. -/
theorem head_le_of_fits (hf : Fits X Y ε) :
    ∀ t, t ≤ X.length + Y.length → (head X Y ε t).i ≤ X.length ∧ (head X Y ε t).j ≤ Y.length
  | 0, _ => by simp
  | t + 1, h => by
    have ih := head_le_of_fits hf t (by omega)
    have hft := hf t (by omega)
    rw [head_i_succ, head_j_succ]
    cases hs : (head X Y ε t).s
    · have := hft.1 hs; simp; omega
    · have := hft.2 hs; simp; omega

/-- **Prefixes are shuffles** (Cloitre's Lemma 2.4): under exact fit, the first `t` outputs contain
exactly the letters consumed from the two tapes. -/
theorem pre_count (hf : Fits X Y ε) (c : Bool) :
    ∀ t, t ≤ X.length + Y.length →
      (pre X Y ε t).count c = (X.take (head X Y ε t).i).count c + (Y.take (head X Y ε t).j).count c
  | 0, _ => by simp
  | t + 1, h => by
    have ih := pre_count hf c t (by omega)
    have hft := hf t (by omega)
    rw [pre_succ, List.count_append, ih, head_i_succ, head_j_succ]
    cases hs : (head X Y ε t).s
    · rw [out_eq_X hf (by omega) hs]
      simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
      rw [List.take_add_one, List.getElem?_eq_getElem (hft.1 hs), Option.toList_some,
        List.count_append]
      omega
    · rw [out_eq_Y hf (by omega) hs]
      simp only [↓reduceIte, Nat.add_zero]
      rw [List.take_add_one (l := Y), List.getElem?_eq_getElem (hft.2 hs), Option.toList_some,
        List.count_append]
      omega

/-- **Heights add** (Cloitre's Lemma 2.4). -/
theorem pre_ht (hf : Fits X Y ε) {t : Nat} (h : t ≤ X.length + Y.length) :
    ht (pre X Y ε t) = ht (X.take (head X Y ε t).i) + ht (Y.take (head X Y ε t).j) := by
  unfold ht
  rw [pre_count hf false t h, pre_count hf true t h]
  omega

/-! ### Head formulas and parked heads -/

/-- **Head formulas** (Cloitre's Lemma 2.5): the `X`-head counts the among.count false the emitted
letters, plus the initial read when `ε = false`. -/
theorem head_i_eq : ∀ t, (head X Y ε (t + 1)).i = (if ε then 0 else 1) + (pre X Y ε t).count false
  | 0 => by cases ε <;> rfl
  | t + 1 => by
    rw [head_i_succ, head_i_eq t, pre_succ, head_s_succ]
    simp only [List.count_append]
    cases out X Y ε t <;> simp <;> omega

/-- The `Y`-head counts the among.count true the emitted letters, plus the initial read when
`ε = true`. -/
theorem head_j_eq : ∀ t, (head X Y ε (t + 1)).j = (if ε then 1 else 0) + (pre X Y ε t).count true
  | 0 => by cases ε <;> rfl
  | t + 1 => by
    rw [head_j_succ, head_j_eq t, pre_succ, head_s_succ]
    simp only [List.count_append]
    cases out X Y ε t <;> simp <;> omega

/-- **Parked `X`-head** (Cloitre's Lemma 3.3): in state `true`, the `X`-head sits just after a one,
unless it has not moved yet. -/
theorem parked_X (hf : Fits X Y ε) :
    ∀ t (ht : t ≤ X.length + Y.length), (head X Y ε t).s = true → ∀ hi : 1 ≤ (head X Y ε t).i,
      X[(head X Y ε t).i - 1]'(by have := head_le_of_fits hf t ht; omega) = true
  | 0, _, _, h => by simp at h
  | t + 1, ht, hs, hi => by
    have hft := hf t (by omega)
    cases hst : (head X Y ε t).s
    · have e := head_i_succ (X := X) (Y := Y) (ε := ε) t
      simp only [hst, Bool.false_eq_true, ↓reduceIte] at e
      have ho : out X Y ε t = true := by rw [← head_s_succ]; exact hs
      rw [out_eq_X hf (by omega) hst] at ho
      simp only [e, Nat.add_sub_cancel]
      exact ho
    · have e := head_i_succ (X := X) (Y := Y) (ε := ε) t
      simp only [hst, ↓reduceIte, Nat.add_zero] at e
      simp only [e]
      exact parked_X hf t (by omega) hst (by omega)

/-- **Parked `Y`-head**: in state `false`, the `Y`-head sits just after a zero, unless it has not
moved yet. -/
theorem parked_Y (hf : Fits X Y ε) :
    ∀ t (ht : t ≤ X.length + Y.length), (head X Y ε t).s = false → ∀ hj : 1 ≤ (head X Y ε t).j,
      Y[(head X Y ε t).j - 1]'(by have := head_le_of_fits hf t ht; omega) = false
  | 0, _, _, h => by simp at h
  | t + 1, ht, hs, hj => by
    have hft := hf t (by omega)
    cases hst : (head X Y ε t).s
    · have e := head_j_succ (X := X) (Y := Y) (ε := ε) t
      simp only [hst, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at e
      simp only [e]
      exact parked_Y hf t (by omega) hst (by omega)
    · have e := head_j_succ (X := X) (Y := Y) (ε := ε) t
      simp only [hst, ↓reduceIte] at e
      have ho : out X Y ε t = false := by rw [← head_s_succ]; exact hs
      rw [out_eq_Y hf (by omega) hst] at ho
      simp only [e, Nat.add_sub_cancel]
      exact ho

/-! ### A counting criterion for exact fit -/

/-- The bookkeeping invariant behind Cloitre's Lemma 2.8: the remaining length of `X` equals the
still.count false to be emitted, counting the current state; and similarly for `Y` and ones. -/
def FitInv (X Y : List Bool) (h : Head) : Prop :=
  h.i ≤ X.length ∧ h.j ≤ Y.length ∧
  X.length - h.i = (X.drop h.i).count false + (Y.drop h.j).count false + (if h.s then 0 else 1) ∧
  Y.length - h.j + 1 = (X.drop h.i).count true + (Y.drop h.j).count true + (if h.s then 1 else 0)

theorem fitInv_step {h : Head} (hI : FitInv X Y h)
    (hX : h.s = false → h.i < X.length) (hY : h.s = true → h.j < Y.length) :
    FitInv X Y (step X Y h) := by
  obtain ⟨hi, hj, e0, e1⟩ := hI
  cases hs : h.s
  · have hx := hX hs
    simp only [hs, Bool.false_eq_true, ↓reduceIte, List.drop_eq_getElem_cons hx,
      List.count_cons] at e0 e1
    simp only [FitInv, step, hs, Bool.false_eq_true, ↓reduceIte,
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hx, Option.getD_some]
    generalize X[h.i] = x at *
    refine ⟨by omega, hj, ?_, ?_⟩ <;> cases x <;> simp_all <;> omega
  · have hy := hY hs
    simp only [hs, ↓reduceIte, List.drop_eq_getElem_cons hy, List.count_cons] at e0 e1
    simp only [FitInv, step, hs, ↓reduceIte,
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hy, Option.getD_some]
    generalize Y[h.j] = y at *
    refine ⟨hi, by omega, ?_, ?_⟩ <;> cases y <;> simp_all <;> omega

/-- **Exact-fit criterion.** If the tape lengths match the letter counts as in `FitInv` and every
nonempty suffix of `X` contains a one, the interleaving has exact fit. Both of Cloitre's laws
satisfy these hypotheses. -/
theorem fits_of_inv
    (h0 : X.length = X.count false + Y.count false + (if ε then 0 else 1))
    (h1 : Y.length + 1 = X.count true + Y.count true + (if ε then 1 else 0))
    (hX : ∀ i, i < X.length → true ∈ X.drop i) : Fits X Y ε := by
  have key : ∀ t, t ≤ X.length + Y.length →
      FitInv X Y (head X Y ε t) ∧ (t < X.length + Y.length →
        ((head X Y ε t).s = false → (head X Y ε t).i < X.length) ∧
        ((head X Y ε t).s = true → (head X Y ε t).j < Y.length)) := by
    intro t
    induction t with
    | zero =>
      intro _
      have hI : FitInv X Y (head X Y ε 0) := by
        simp only [FitInv, head_zero, Nat.zero_le, List.drop_zero, Nat.sub_zero, true_and]
        exact ⟨h0, h1⟩
      refine ⟨hI, fun hlt => ?_⟩
      obtain ⟨-, -, e0, e1⟩ := hI
      simp only [head_zero] at e0 e1 ⊢
      refine ⟨fun hs => ?_, fun hs => ?_⟩
      · simp only [hs, Bool.false_eq_true, ↓reduceIte] at e0; omega
      · simp only [hs, ↓reduceIte] at e1
        rcases Nat.lt_or_ge 0 Y.length with hy | hy
        · exact hy
        · have hx : 0 < X.length := by omega
          have := List.count_pos_iff.2 (hX 0 hx)
          omega
    | succ t ih =>
      intro ht
      obtain ⟨hI, hfit⟩ := ih (by omega)
      have hI' := fitInv_step hI (hfit (by omega)).1 (hfit (by omega)).2
      rw [← head_succ] at hI'
      refine ⟨hI', fun hlt => ?_⟩
      have hij := head_i_add_j (X := X) (Y := Y) (ε := ε) (t + 1)
      obtain ⟨hi, hj, e0, e1⟩ := hI'
      refine ⟨fun hs => ?_, fun hs => ?_⟩
      · simp only [hs, Bool.false_eq_true, ↓reduceIte] at e0; omega
      · simp only [hs, ↓reduceIte] at e1
        rcases Nat.lt_or_ge (head X Y ε (t + 1)).j Y.length with hy | hy
        · exact hy
        · have hx : (head X Y ε (t + 1)).i < X.length := by omega
          have := List.count_pos_iff.2 (hX _ hx)
          omega
  exact fun t ht => (key t (Nat.le_of_lt ht)).2 ht

/-- Under exact fit, the machine ends with both tapes consumed. -/
theorem head_end (hf : Fits X Y ε) :
    (head X Y ε (X.length + Y.length)).i = X.length ∧
    (head X Y ε (X.length + Y.length)).j = Y.length := by
  have h := head_le_of_fits hf _ (Nat.le_refl _)
  have := head_i_add_j (X := X) (Y := Y) (ε := ε) (X.length + Y.length)
  omega

/-- Under exact fit, the output is a shuffle of the two tapes. -/
theorem count_interleave (hf : Fits X Y ε) (c : Bool) :
    (interleave X Y ε).count c = X.count c + Y.count c := by
  rw [interleave, pre_count hf c _ (Nat.le_refl _), (head_end hf).1, (head_end hf).2,
    List.take_length, List.take_length]

end QTilde
