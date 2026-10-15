
/-! ## Certificates with an exempt ("bad") rank class

A *bad-class certificate* is a `Cert` together with a rank `bad`.  Edges never increase the rank; inside
every rank class other than `bad` the position labelling is consistent (as in `Cert.check`).  Along the
true history the rank is eventually constant; if the final class were not `bad`, column 1 at the white
times would be periodic and `masked_jen` gives a contradiction.  Hence, if the center column is eventually
`w`-periodic, the strip of the true right half eventually stays in the bad class forever. -/

namespace R30Skel
open Ruliology.CellularAutomata.Rule30Jen

namespace Cert
variable (C : Cert)

/-- Edge condition with the rank class `bad` exempt from the labelling requirement. -/
def edgeOKb (bad φ : Nat) (s s' : List Bool) : Bool :=
  let φ' := (φ + 1) % C.P
  let r := C.rk φ s
  decide (C.rk φ' s' ≤ r) &&
  (!(C.rk φ' s' == r) || (r == bad) ||
    ((C.ps φ' s' == C.nextPos r (C.ps φ s) φ) && (C.wAt φ || (s.headD false == C.u r (C.ps φ s)))))

def checkb (bad : Nat) : Bool :=
  (List.range C.P).all fun φ => (allLists C.b).all fun s =>
    [false, true].all fun x => C.edgeOKb bad φ s (lin3 (C.wAt φ :: (s ++ [x])))

def checkGb (bad : Nat) : Bool :=
  (List.range C.nranks).all (fun r => (r == bad) || (decide (0 < C.m r) &&
    ((List.range (C.m r)).all fun p => (List.range C.P).all fun φ =>
      C.iterG r (C.m r * C.P) (p, φ) == (p, φ)))) &&
  ((List.range C.P).all fun φ => (allLists C.b).all fun s =>
    decide (C.rk φ s < C.nranks) && ((C.rk φ s == bad) || decide (C.ps φ s < C.m (C.rk φ s))))

/-- Every node of the bad class satisfies `pred`. -/
def badImp (bad : Nat) (pred : Nat → List Bool → Bool) : Bool :=
  (List.range C.P).all fun φ => (allLists C.b).all fun s => !(C.rk φ s == bad) || pred φ s

end Cert

theorem Cert.sound_bad (C : Cert) (bad : Nat) (hC : C.checkb bad = true) (hG : C.checkGb bad = true)
    (hP : 0 < C.P) (hb : 0 < C.b)
    (T : Nat) (h : ∀ t, T ≤ t → cell t 0 = C.wAt ((t - T) % C.P)) :
    ∃ T', T ≤ T' ∧ ∀ t, T' ≤ t → C.rk ((t - T) % C.P) (rowR t C.b) = bad := by
  let ph : Nat → Nat := fun t => (t - T) % C.P
  let st : Nat → List Bool := fun t => rowR t C.b
  have hph : ∀ t, T ≤ t → ph (t + 1) = (ph t + 1) % C.P := by
    intro t ht
    show (t + 1 - T) % C.P = ((t - T) % C.P + 1) % C.P
    rw [show t + 1 - T = (t - T) + 1 by omega]
    exact (Nat.mod_add_mod (t - T) C.P 1).symm
  have hphlt : ∀ t, ph t < C.P := fun t => Nat.mod_lt _ hP
  have hedge : ∀ t, T ≤ t → C.edgeOKb bad (ph t) (st t) (st (t + 1)) = true := by
    intro t ht
    have hall := hC
    unfold Cert.checkb at hall
    have h1 := List.all_eq_true.1 hall (ph t) (List.mem_range.2 (hphlt t))
    have h2 := List.all_eq_true.1 h1 (st t) (allLists_mem _ _ (rowR_length t C.b))
    have h3 := List.all_eq_true.1 h2 (cell t ((C.b : Int) + 1)) (by cases cell t ((C.b : Int) + 1) <;> simp)
    have hs : st (t + 1) = lin3 (C.wAt (ph t) :: (st t ++ [cell t ((C.b : Int) + 1)])) := by
      show rowR (t + 1) C.b = _
      rw [rowR_succ, h t ht]
    rw [hs]; exact h3
  let R : Nat → Nat := fun t => C.rk (ph t) (st t)
  have hRle : ∀ t, T ≤ t → R (t + 1) ≤ R t := by
    intro t ht
    have e := hedge t ht
    unfold Cert.edgeOKb at e
    simp only [Bool.and_eq_true, decide_eq_true_eq] at e
    show C.rk (ph (t + 1)) (st (t + 1)) ≤ C.rk (ph t) (st t)
    rw [hph t ht]; exact e.1
  obtain ⟨T', hT', hconst⟩ := antitone_eventually_const R T hRle
  refine ⟨T', hT', fun t₀ ht₀ => ?_⟩
  show R t₀ = bad
  rw [hconst t₀ ht₀]
  refine Classical.byContradiction fun hne => ?_
  let r := R T'
  have hrb : (r == bad) = false := by
    cases hq : (r == bad) with
    | false => rfl
    | true => exact absurd (beq_iff_eq.1 hq) hne
  have hstep : ∀ t, T' ≤ t →
      C.ps (ph (t + 1)) (st (t + 1)) = C.nextPos r (C.ps (ph t) (st t)) (ph t) ∧
      (C.wAt (ph t) = false → cell t 1 = C.u r (C.ps (ph t) (st t))) := by
    intro t ht
    have e := hedge t (by omega)
    have hRt : R t = r := hconst t ht
    have hRt1 : R (t + 1) = r := hconst (t + 1) (by omega)
    unfold Cert.edgeOKb at e
    rw [← hph t (by omega)] at e
    have hr1 : C.rk (ph (t + 1)) (st (t + 1)) = C.rk (ph t) (st t) := by
      show R (t + 1) = R t; rw [hRt, hRt1]
    have hrt : C.rk (ph t) (st t) = r := hRt
    simp only [hr1, hrt, hrb, beq_self_eq_true, Bool.not_true, Bool.false_or, Bool.and_eq_true, beq_iff_eq,
      decide_eq_true_eq] at e
    refine ⟨e.2.1, fun hw => ?_⟩
    have e2 := e.2.2
    rw [hw, Bool.false_or, beq_iff_eq] at e2
    rw [← rowR_head t C.b hb]; exact e2
  let q : Nat → Nat × Nat := fun t => (C.ps (ph t) (st t), ph t)
  have hq : ∀ t, T' ≤ t → q (t + 1) = C.G r (q t) := by
    intro t ht
    show (C.ps (ph (t + 1)) (st (t + 1)), ph (t + 1)) = (C.nextPos r (C.ps (ph t) (st t)) (ph t), (ph t + 1) % C.P)
    rw [(hstep t ht).1, hph t (by omega)]
  have hqiter : ∀ t, T' ≤ t → ∀ n, q (t + n) = C.iterG r n (q t) := by
    intro t ht n
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [show t + (n + 1) = (t + n) + 1 by omega, hq (t + n) (by omega), ih,
        show n + 1 = n + 1 from rfl, iterG_add C r n 1 (q t)]
      rfl
  have hG' := hG
  unfold Cert.checkGb at hG'
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq, beq_iff_eq,
    Bool.or_eq_true] at hG'
  obtain ⟨hGr, hGn⟩ := hG'
  have hrlt : r < C.nranks := (hGn (ph T') (hphlt T') (st T') (allLists_mem _ _ (rowR_length T' C.b))).1
  have hrne : r ≠ bad := hne
  have hGr' := (hGr r hrlt).resolve_left hrne
  have hm : 0 < C.m r := hGr'.1
  have hper : ∀ t, T' ≤ t → q (t + C.m r * C.P) = q t := by
    intro t ht
    rw [hqiter t ht]
    have hrt : C.rk (ph t) (st t) = r := hconst t ht
    have hpos0 := (hGn (ph t) (hphlt t) (st t) (allLists_mem _ _ (rowR_length t C.b))).2
    rw [hrt] at hpos0
    have hpos : C.ps (ph t) (st t) < C.m r := hpos0.resolve_left hrne
    exact hGr'.2 _ hpos _ (hphlt t)
  refine masked_jen 0 (Q := C.m r * C.P) (Nat.mul_pos hm hP) (T := T') ?_ ?_
  · intro t ht
    rw [h (t + C.m r * C.P) (by omega), h t (by omega)]
    congr 1
    rw [show t + C.m r * C.P - T = (t - T) + C.P * C.m r by rw [Nat.mul_comm]; omega, Nat.add_mul_mod_self_left]
  · intro t ht hw
    rw [show (0 : Int) + 1 = 1 by rfl]
    have hwt : C.wAt (ph t) = false := by rw [← h t (by omega)]; exact hw
    have hqe := hper t ht
    have hph' : ph (t + C.m r * C.P) = ph t := congrArg Prod.snd hqe
    have hps' : C.ps (ph (t + C.m r * C.P)) (st (t + C.m r * C.P)) = C.ps (ph t) (st t) := congrArg Prod.fst hqe
    have hwt' : C.wAt (ph (t + C.m r * C.P)) = false := by rw [hph']; exact hwt
    rw [(hstep (t + C.m r * C.P) (by omega)).2 hwt', (hstep t ht).2 hwt, hps']

/-- Consequence: every predicate checked on the bad class holds eventually along the true history. -/
theorem Cert.eventually_pred (C : Cert) (bad : Nat) (pred : Nat → List Bool → Bool)
    (hC : C.checkb bad = true) (hG : C.checkGb bad = true) (hI : C.badImp bad pred = true)
    (hP : 0 < C.P) (hb : 0 < C.b)
    (T : Nat) (h : ∀ t, T ≤ t → cell t 0 = C.wAt ((t - T) % C.P)) :
    ∃ T', T ≤ T' ∧ ∀ t, T' ≤ t → pred ((t - T) % C.P) (rowR t C.b) = true := by
  obtain ⟨T', hT', hbad⟩ := Cert.sound_bad C bad hC hG hP hb T h
  refine ⟨T', hT', fun t ht => ?_⟩
  have hall := hI
  unfold Cert.badImp at hall
  have h1 := List.all_eq_true.1 hall ((t - T) % C.P) (List.mem_range.2 (Nat.mod_lt _ hP))
  have h2 := List.all_eq_true.1 h1 (rowR t C.b) (allLists_mem _ _ (rowR_length t C.b))
  rw [hbad t ht] at h2
  simpa using h2

theorem seg_getD (f : Nat → Bool) : ∀ (n i : Nat), i < n → (seg f n).getD i false = f i
  | 0, i, h => absurd h (Nat.not_lt_zero _)
  | n + 1, 0, _ => rfl
  | n + 1, i + 1, h => by
    show (seg (fun j => f (j + 1)) n).getD i false = f (i + 1)
    exact seg_getD (fun j => f (j + 1)) n i (by omega)

theorem rowR_getD (t m i : Nat) (h : i < m) : (rowR t m).getD i false = cell t ((i : Int) + 1) :=
  seg_getD _ m i h

end R30Skel
