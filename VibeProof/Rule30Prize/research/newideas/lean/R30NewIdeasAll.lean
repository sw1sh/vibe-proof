import Ruliology.CellularAutomata.Rule30Jen

/-!
# Strip certificates: excluding a periodic tail `w^∞` of the center column by a finite computation

Suppose the center column equals `w^∞` (phase `(t - T) % P`) from time `T` on.  The cells `1..b` of the
right half then evolve as a finite nondeterministic system: the next strip is
`lin3 (c :: s ++ [x])`, where `c` is the center cell and `x = cell t (b+1)` is unknown.

A *certificate* assigns to every node `(phase, strip)` a rank and a position such that along every edge
the rank does not increase, and along every rank-preserving edge the position advances like a counter
modulo `m` (only at the white phases of `w`) and, at white phases, column 1 is the `pos`-th letter of a
fixed word.  Along the true history the rank is eventually constant, after which column 1 restricted to
the white times is periodic; `masked_jen` (Jen's theorem with the right neighbour masked by the zeros of
the column) gives the contradiction.

`Cert.sound` is the soundness theorem; the checks `Cert.check`, `Cert.checkG` are Boolean computations
discharged by `decide` for each concrete certificate.
-/

namespace R30NewIdeas
open Ruliology.CellularAutomata.Rule30Jen

/-! ### Masked Jen -/

theorem masked_jen (i : Int) {T Q : Nat} (hQ : 0 < Q)
    (h0 : ∀ t, T ≤ t → cell (t + Q) i = cell t i)
    (h1 : ∀ t, T ≤ t → cell t i = false → cell (t + Q) (i + 1) = cell t (i + 1)) : False := by
  have hm : ∀ t, T ≤ t → cell (t + Q) (i - 1) = cell t (i - 1) := by
    intro t ht
    rw [cell_left (t + Q) i, cell_left t i, show t + Q + 1 = (t + 1) + Q by omega,
      h0 (t + 1) (by omega), h0 t ht]
    cases hc : cell t i with
    | false => rw [h1 t ht hc]
    | true => rfl
  have e : i - 1 + 1 = i := by omega
  refine not_adjacent (i - 1) ⟨T, Q, hQ, hm⟩ ?_
  rw [e]
  exact ⟨T, Q, hQ, h0⟩

/-! ### The right strip as lists -/

def lin3 : List Bool → List Bool
  | a :: b :: c :: rest => xor a (b || c) :: lin3 (b :: c :: rest)
  | _ => []

def seg (f : Nat → Bool) : Nat → List Bool
  | 0 => []
  | n + 1 => f 0 :: seg (fun i => f (i + 1)) n

theorem lin3_seg : ∀ (m : Nat) (f : Nat → Bool),
    lin3 (seg f (m + 2)) = seg (fun i => xor (f i) (f (i + 1) || f (i + 2))) m
  | 0, f => rfl
  | m + 1, f => by
    show xor (f 0) (f 1 || f 2) :: lin3 (seg (fun i => f (i + 1)) (m + 2)) = _
    rw [lin3_seg m (fun i => f (i + 1))]
    rfl

theorem seg_succ : ∀ (n : Nat) (f : Nat → Bool), seg f (n + 1) = seg f n ++ [f n]
  | 0, f => rfl
  | n + 1, f => by
    show f 0 :: seg (fun i => f (i + 1)) (n + 1) = f 0 :: (seg (fun i => f (i + 1)) n ++ [f (n + 1)])
    rw [seg_succ n (fun i => f (i + 1))]

theorem length_seg : ∀ (n : Nat) (f : Nat → Bool), (seg f n).length = n
  | 0, _ => rfl
  | n + 1, f => by simp [seg, length_seg n]

/-- Columns `1..m` at time `t`. -/
def rowR (t m : Nat) : List Bool := seg (fun i => cell t ((i : Int) + 1)) m

theorem cons_rowR (t m : Nat) :
    cell t 0 :: rowR t m = seg (fun i => cell t (i : Int)) (m + 1) := by
  show cell t 0 :: seg (fun i => cell t ((i : Int) + 1)) m = cell t ((0 : Nat) : Int) :: seg _ m
  congr 2

/-- One step of the strip: the new strip is `lin3` of the old one with the center cell in front and
cell `b+1` at the end. -/
theorem rowR_succ (t b : Nat) :
    rowR (t + 1) b = lin3 (cell t 0 :: (rowR t b ++ [cell t ((b : Int) + 1)])) := by
  have e1 : rowR t b ++ [cell t ((b : Int) + 1)] = rowR t (b + 1) := by
    unfold rowR; rw [seg_succ]
  rw [e1, cons_rowR, lin3_seg]
  unfold rowR
  congr 1
  funext i
  show rule (cell t ((i : Int) + 1 - 1)) (cell t ((i : Int) + 1)) (cell t ((i : Int) + 1 + 1)) =
    xor (cell t (i : Int)) (cell t ((i + 1 : Nat) : Int) || cell t ((i + 2 : Nat) : Int))
  rw [show ((i : Int) + 1 - 1) = (i : Int) by omega, show ((i + 1 : Nat) : Int) = (i : Int) + 1 by omega,
    show ((i + 2 : Nat) : Int) = (i : Int) + 1 + 1 by omega]
  rfl

theorem rowR_length (t b : Nat) : (rowR t b).length = b := length_seg b _

theorem rowR_head (t b : Nat) (hb : 0 < b) : (rowR t b).headD false = cell t 1 := by
  obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
  rfl

/-! ### Certificates -/

/-- Little-endian encoding of a strip. -/
def enc : List Bool → Nat
  | [] => 0
  | x :: l => (if x then 1 else 0) + 2 * enc l

/-- A certificate with packed tables: `rankP` (16-bit fields indexed by node), `posP` (8-bit fields by
node), `perP` (8-bit fields by rank), `wordP` (64-bit fields by rank, bit `p` = letter `p`). -/
structure Cert where
  w : List Bool
  b : Nat
  nranks : Nat
  rankP : Nat
  posP : Nat
  perP : Nat
  wordP : Nat

namespace Cert
variable (C : Cert)

def P : Nat := C.w.length
def wAt (φ : Nat) : Bool := C.w.getD φ false
def idx (φ : Nat) (s : List Bool) : Nat := φ * 2 ^ C.b + enc s
def rk (φ : Nat) (s : List Bool) : Nat := (C.rankP >>> (16 * C.idx φ s)) % 65536
def ps (φ : Nat) (s : List Bool) : Nat := (C.posP >>> (8 * C.idx φ s)) % 256
def m (r : Nat) : Nat := (C.perP >>> (8 * r)) % 256
def u (r p : Nat) : Bool := (C.wordP >>> (64 * r + p)) % 2 == 1

/-- Counter update at phase `φ` inside rank class `r`. -/
def nextPos (r p φ : Nat) : Nat := if C.wAt φ then p else (p + 1) % C.m r

/-- The edge condition for `(φ, s) → ((φ+1) % P, s')`. -/
def edgeOK (φ : Nat) (s s' : List Bool) : Bool :=
  let φ' := (φ + 1) % C.P
  let r := C.rk φ s
  decide (C.rk φ' s' ≤ r) &&
  (!(C.rk φ' s' == r) ||
    ((C.ps φ' s' == C.nextPos r (C.ps φ s) φ) && (C.wAt φ || (s.headD false == C.u r (C.ps φ s)))))

def check : Bool :=
  (List.range C.P).all fun φ => (allLists C.b).all fun s =>
    [false, true].all fun x => C.edgeOK φ s (lin3 (C.wAt φ :: (s ++ [x])))

/-- The counter-phase map `G (p, φ) = (nextPos p φ, (φ+1) % P)`. -/
def G (r : Nat) (q : Nat × Nat) : Nat × Nat := (C.nextPos r q.1 q.2, (q.2 + 1) % C.P)

end Cert

def Cert.iterG (C : Cert) (r : Nat) : Nat → Nat × Nat → Nat × Nat
  | 0, q => q
  | n + 1, q => Cert.iterG C r n (C.G r q)

namespace Cert
variable (C : Cert)

/-- Every node's position is below its period, every period is positive, and `G^(m P) = id`. -/
def checkG : Bool :=
  (List.range C.nranks).all (fun r => decide (0 < C.m r) &&
    ((List.range (C.m r)).all fun p => (List.range C.P).all fun φ =>
      C.iterG r (C.m r * C.P) (p, φ) == (p, φ))) &&
  ((List.range C.P).all fun φ => (allLists C.b).all fun s =>
    decide (C.rk φ s < C.nranks) && decide (C.ps φ s < C.m (C.rk φ s)))

end Cert

/-! ### Soundness -/

theorem allLists_mem (l : List Bool) (n : Nat) (h : l.length = n) : l ∈ allLists n := by
  subst h; exact mem_allLists l

theorem antitone_eventually_const (f : Nat → Nat) (T : Nat) (h : ∀ t, T ≤ t → f (t + 1) ≤ f t) :
    ∃ T', T ≤ T' ∧ ∀ t, T' ≤ t → f t = f T' := by
  have mono : ∀ t s, T ≤ t → f (t + s) ≤ f t := by
    intro t s ht
    induction s with
    | zero => exact Nat.le_refl _
    | succ s ih => exact Nat.le_trans (h (t + s) (by omega)) ih
  -- strong induction on the value f T
  suffices H : ∀ n, ∀ T₀, T ≤ T₀ → f T₀ ≤ n → ∃ T', T₀ ≤ T' ∧ ∀ t, T' ≤ t → f t = f T' by
    obtain ⟨T', h1, h2⟩ := H (f T) T (Nat.le_refl _) (Nat.le_refl _)
    exact ⟨T', h1, h2⟩
  intro n
  induction n with
  | zero =>
    intro T₀ hT₀ hf
    refine ⟨T₀, Nat.le_refl _, fun t ht => ?_⟩
    have := mono T₀ (t - T₀) hT₀
    rw [show T₀ + (t - T₀) = t by omega] at this
    omega
  | succ n ih =>
    intro T₀ hT₀ hf
    by_cases hc : ∀ t, T₀ ≤ t → f t = f T₀
    · exact ⟨T₀, Nat.le_refl _, hc⟩
    · have : ∃ t, T₀ ≤ t ∧ f t ≠ f T₀ := by
        refine Classical.byContradiction fun hn => hc fun t ht => ?_
        exact Classical.byContradiction fun hne => hn ⟨t, ht, hne⟩
      obtain ⟨t₁, ht₁, hne⟩ := this
      have hle := mono T₀ (t₁ - T₀) hT₀
      rw [show T₀ + (t₁ - T₀) = t₁ by omega] at hle
      obtain ⟨T', h1, h2⟩ := ih t₁ (by omega) (by omega)
      exact ⟨T', by omega, h2⟩

theorem iterG_add (C : Cert) (r : Nat) : ∀ (a n : Nat) (q : Nat × Nat), C.iterG r (a + n) q = C.iterG r n (C.iterG r a q)
  | 0, n, q => by simp [Cert.iterG]
  | a + 1, n, q => by
    rw [show a + 1 + n = (a + n) + 1 by omega]
    show C.iterG r (a + n) (C.G r q) = C.iterG r n (C.iterG r a (C.G r q))
    exact iterG_add C r a n (C.G r q)

theorem Cert.sound (C : Cert) (hC : C.check = true) (hG : C.checkG = true) (hP : 0 < C.P) (hb : 0 < C.b)
    (T : Nat) (h : ∀ t, T ≤ t → cell t 0 = C.wAt ((t - T) % C.P)) : False := by
  -- the history
  let ph : Nat → Nat := fun t => (t - T) % C.P
  let st : Nat → List Bool := fun t => rowR t C.b
  have hph : ∀ t, T ≤ t → ph (t + 1) = (ph t + 1) % C.P := by
    intro t ht
    show (t + 1 - T) % C.P = ((t - T) % C.P + 1) % C.P
    rw [show t + 1 - T = (t - T) + 1 by omega]
    exact (Nat.mod_add_mod (t - T) C.P 1).symm
  have hphlt : ∀ t, ph t < C.P := fun t => Nat.mod_lt _ hP
  -- every true step is an edge of the certificate graph, hence satisfies edgeOK
  have hedge : ∀ t, T ≤ t → C.edgeOK (ph t) (st t) (st (t + 1)) = true := by
    intro t ht
    have hall := hC
    unfold Cert.check at hall
    have h1 := List.all_eq_true.1 hall (ph t) (List.mem_range.2 (hphlt t))
    have h2 := List.all_eq_true.1 h1 (st t) (allLists_mem _ _ (rowR_length t C.b))
    have h3 := List.all_eq_true.1 h2 (cell t ((C.b : Int) + 1)) (by cases cell t ((C.b : Int) + 1) <;> simp)
    have hs : st (t + 1) = lin3 (C.wAt (ph t) :: (st t ++ [cell t ((C.b : Int) + 1)])) := by
      show rowR (t + 1) C.b = _
      rw [rowR_succ, h t ht]
    rw [hs]; exact h3
  -- rank along the history
  let R : Nat → Nat := fun t => C.rk (ph t) (st t)
  have hRle : ∀ t, T ≤ t → R (t + 1) ≤ R t := by
    intro t ht
    have e := hedge t ht
    unfold Cert.edgeOK at e
    simp only [Bool.and_eq_true, decide_eq_true_eq] at e
    show C.rk (ph (t + 1)) (st (t + 1)) ≤ C.rk (ph t) (st t)
    rw [hph t ht]; exact e.1
  obtain ⟨T', hT', hconst⟩ := antitone_eventually_const R T hRle
  let r := R T'
  -- along rank-preserving steps: counter update and output
  have hstep : ∀ t, T' ≤ t →
      C.ps (ph (t + 1)) (st (t + 1)) = C.nextPos r (C.ps (ph t) (st t)) (ph t) ∧
      (C.wAt (ph t) = false → cell t 1 = C.u r (C.ps (ph t) (st t))) := by
    intro t ht
    have e := hedge t (by omega)
    have hRt : R t = r := hconst t ht
    have hRt1 : R (t + 1) = r := hconst (t + 1) (by omega)
    unfold Cert.edgeOK at e
    rw [← hph t (by omega)] at e
    have hr1 : C.rk (ph (t + 1)) (st (t + 1)) = C.rk (ph t) (st t) := by
      show R (t + 1) = R t; rw [hRt, hRt1]
    simp only [hr1, beq_self_eq_true, Bool.not_true, Bool.false_or, Bool.and_eq_true, beq_iff_eq,
      decide_eq_true_eq] at e
    have hrt : C.rk (ph t) (st t) = r := hRt
    rw [hrt] at e
    refine ⟨e.2.1, fun hw => ?_⟩
    have e2 := e.2.2
    rw [hw, Bool.false_or, beq_iff_eq] at e2
    rw [← rowR_head t C.b hb]; exact e2
  -- the counter-phase pair follows G
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
  -- checkG facts
  have hG' := hG
  unfold Cert.checkG at hG'
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq, beq_iff_eq] at hG'
  obtain ⟨hGr, hGn⟩ := hG'
  have hrlt : r < C.nranks := (hGn (ph T') (hphlt T') (st T') (allLists_mem _ _ (rowR_length T' C.b))).1
  have hm : 0 < C.m r := (hGr r hrlt).1
  -- periodicity of the counter-phase pair after T'
  have hper : ∀ t, T' ≤ t → q (t + C.m r * C.P) = q t := by
    intro t ht
    rw [hqiter t ht]
    have hpos : C.ps (ph t) (st t) < C.m (C.rk (ph t) (st t)) :=
      (hGn (ph t) (hphlt t) (st t) (allLists_mem _ _ (rowR_length t C.b))).2
    have hrt : C.rk (ph t) (st t) = r := hconst t ht
    rw [hrt] at hpos
    exact (hGr r hrlt).2 _ hpos _ (hphlt t)
  -- conclude with masked Jen, Q = m * P
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


/-! ### Consequences of masked Jen for the center column -/

/-- The masked pair `(c t, !c t && col₁ t)` of the center column is not eventually periodic.
Equivalently: if the center column is eventually periodic, column 1 restricted to the zeros of the
center column is not eventually periodic (for any common period). -/
theorem center_masked_not_eventually_periodic :
    ¬ ∃ T Q : Nat, 0 < Q ∧ ∀ t, T ≤ t →
      cell (t + Q) 0 = cell t 0 ∧ (cell t 0 = false → cell (t + Q) 1 = cell t 1) := by
  rintro ⟨T, Q, hQ, h⟩
  exact masked_jen 0 hQ (fun t ht => (h t ht).1) (fun t ht hc => by simpa using (h t ht).2 hc)

/-- At a black center cell the left neighbour is forced: `c t = true → cell t (-1) = !c (t+1)`. -/
theorem left_of_black_center (t : Nat) (h : cell t 0 = true) : cell t (-1) = !cell (t + 1) 0 := by
  have := cell_left t 0
  simp only [h, Bool.true_or] at this
  rw [show (0 : Int) - 1 = -1 by rfl] at this
  rw [this]; cases cell (t + 1) 0 <;> rfl


/-! ### Black runs: nine black center cells force columns 1 and 2 -/

/-- `k` steps of the right strip with column 0 held at `c0`. -/
def iterR (c0 : Bool) : Nat → List Bool → List Bool
  | 0, row => row
  | k + 1, row => iterR c0 k (lin3 (c0 :: row))

/-- All `2^11` rows: nine black center steps make column 1 white and column 2 black. -/
theorem black9_check : ∀ b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 : Bool,
    iterR true 9 [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11] = [false, true] := by
  decide

theorem lin3_rowR (t m : Nat) (h : cell t 0 = true) : lin3 (true :: rowR t (m + 1)) = rowR (t + 1) m := by
  rw [← h, cons_rowR, lin3_seg]
  unfold rowR
  congr 1
  funext i
  show xor (cell t (i : Int)) (cell t ((i + 1 : Nat) : Int) || cell t ((i + 2 : Nat) : Int)) =
    rule (cell t ((i : Int) + 1 - 1)) (cell t ((i : Int) + 1)) (cell t ((i : Int) + 1 + 1))
  rw [show ((i : Int) + 1 - 1) = (i : Int) by omega, show ((i + 1 : Nat) : Int) = (i : Int) + 1 by omega,
    show ((i + 2 : Nat) : Int) = (i : Int) + 1 + 1 by omega]
  rfl

theorem iterR_rowR : ∀ (k n t : Nat), (∀ j, j < k → cell (t + j) 0 = true) →
    iterR true k (rowR t (n + k)) = rowR (t + k) n
  | 0, n, t, _ => rfl
  | k + 1, n, t, h => by
    show iterR true k (lin3 (true :: rowR t (n + k + 1))) = _
    rw [lin3_rowR t (n + k) (by simpa using h 0 (by omega))]
    rw [iterR_rowR k n (t + 1) (fun j hj => by rw [show t + 1 + j = t + (j + 1) by omega]; exact h (j + 1) (by omega))]
    rw [show t + 1 + k = t + (k + 1) by omega]

/-- **Black-run lemma.** Nine consecutive black center cells force column 1 white and column 2 black. -/
theorem black_run (t : Nat) (h : ∀ j, j < 9 → cell (t + j) 0 = true) :
    cell (t + 9) 1 = false ∧ cell (t + 9) 2 = true := by
  have e := iterR_rowR 9 2 t h
  have hrow : rowR t (2 + 9) = [cell t 1, cell t 2, cell t 3, cell t 4, cell t 5, cell t 6, cell t 7,
      cell t 8, cell t 9, cell t 10, cell t 11] := rfl
  rw [hrow, black9_check] at e
  have hrow2 : rowR (t + 9) 2 = [cell (t + 9) 1, cell (t + 9) 2] := rfl
  rw [hrow2] at e
  simp only [List.cons.injEq] at e
  exact ⟨e.1.symm, e.2.1.symm⟩

/-- Inside a white run of the center column that follows nine black cells, column 1 is white at the
first white time and black afterwards. -/
theorem col1_after_black_run (z : Nat) (h9 : ∀ j, j < 9 → cell (z - 9 + j) 0 = true) (hz : 9 ≤ z) :
    ∀ k, (∀ i, i ≤ k → cell (z + i) 0 = false) → cell (z + k) 1 = decide (0 < k) := by
  have hb := black_run (z - 9) h9
  rw [show z - 9 + 9 = z by omega] at hb
  intro k
  induction k with
  | zero => intro _; simpa using hb.1
  | succ k ih =>
    intro hw
    have hwk : cell (z + k) 0 = false := hw k (by omega)
    show rule (cell (z + k) (1 - 1)) (cell (z + k) 1) (cell (z + k) (1 + 1)) = decide (0 < k + 1)
    rw [show (1 : Int) - 1 = 0 by rfl, hwk]
    cases k with
    | zero => simp [rule, hb.2]
    | succ k =>
      rw [ih (fun i hi => hw i (by omega))]
      simp [rule]

/-- **Corollary of the black-run lemma.** If the center column is eventually periodic, it is not the
case that (from some time on) every white cell lies in a white run preceded by at least nine black
cells. -/
theorem not_eventually_periodic_of_long_black_runs (T P T' : Nat) (hP : 0 < P)
    (hper : ∀ t, T ≤ t → cell (t + P) 0 = cell t 0)
    (hrun : ∀ t, T' ≤ t → cell t 0 = false → ∃ k, k + 10 ≤ t ∧ (∀ i, i ≤ k → cell (t - i) 0 = false) ∧
      (∀ j, j < 9 → cell (t - k - 9 + j) 0 = true)) : False := by
  -- column 1 at white times is the negation of the previous center cell
  have key : ∀ t, T' ≤ t → cell t 0 = false → cell t 1 = !cell (t - 1) 0 := by
    intro t ht hw
    obtain ⟨k, hk, hwhite, hblack⟩ := hrun t ht hw
    have := col1_after_black_run (t - k) (fun j hj => hblack j hj) (by omega) k
      (fun i hi => by rw [show t - k + i = t - (k - i) by omega]; exact hwhite (k - i) (by omega))
    rw [show t - k + k = t by omega] at this
    rw [this]
    cases k with
    | zero =>
      have hb : cell (t - 1) 0 = true := by
        have := hblack 8 (by omega); rwa [show t - 0 - 9 + 8 = t - 1 by omega] at this
      simp [hb]
    | succ k =>
      have hw1 : cell (t - 1) 0 = false := hwhite 1 (by omega)
      simp [hw1]
  refine masked_jen 0 hP (T := max T T' + 1) (fun t ht => hper t (by omega)) ?_
  intro t ht hw
  have hw' : cell (t + P) 0 = false := by rw [hper t (by omega)]; exact hw
  rw [show (0 : Int) + 1 = 1 by rfl]
  rw [key t (by omega) hw, key (t + P) (by omega) hw', show t + P - 1 = (t - 1) + P by omega,
    hper (t - 1) (by omega)]

/-- Instance: for every `k ≥ 9`, the center column is not eventually `(0 1^k)`-periodic, i.e. there is
no `T` with `cell t 0 = decide ((t - T) % (k+1) ≠ 0)` for all `t ≥ T`. -/
theorem not_eventually_zero_ones (k : Nat) (hk : 9 ≤ k) (T : Nat)
    (h : ∀ t, T ≤ t → cell t 0 = decide ((t - T) % (k + 1) ≠ 0)) : False := by
  refine not_eventually_periodic_of_long_black_runs T (k + 1) (T + k + 11) (by omega) ?_ ?_
  · intro t ht
    rw [h (t + (k + 1)) (by omega), h t ht, show t + (k + 1) - T = (t - T) + (k + 1) by omega,
      Nat.add_mod_right]
  · intro t ht hw
    rw [h t (by omega)] at hw
    have hz : (t - T) % (k + 1) = 0 := by simpa using hw
    refine ⟨0, by omega, fun i hi => ?_, fun j hj => ?_⟩
    · rw [show i = 0 by omega, Nat.sub_zero, h t (by omega)]; simpa using hz
    · rw [h _ (by omega)]
      simp only [decide_eq_true_eq]
      intro hm
      -- (t - T) ≡ 0 and t - 9 + j - T = (t - T) - (9 - j) with 1 ≤ 9 - j ≤ 9 < k + 1
      have e : t - 0 - 9 + j - T = (t - T) - (9 - j) := by omega
      rw [e] at hm
      have h1 : (t - T) = (k + 1) * ((t - T) / (k + 1)) := by
        have := Nat.div_add_mod (t - T) (k + 1); omega
      have hq : 1 ≤ (t - T) / (k + 1) := by
        rcases Nat.eq_zero_or_pos ((t - T) / (k + 1)) with h0 | h0
        · rw [h0] at h1; omega
        · exact h0
      have : (t - T) - (9 - j) = (k + 1) * ((t - T) / (k + 1) - 1) + (k + 1 - (9 - j)) := by
        rw [Nat.mul_sub, Nat.mul_one]; omega
      rw [this, Nat.mul_add_mod] at hm
      rw [Nat.mod_eq_of_lt (by omega)] at hm
      omega


/-! ### Rigid structure under an alternating center column -/

theorem step_eq (t : Nat) (p : Int) : cell (t + 1) p = xor (cell t (p - 1)) (cell t p || cell t (p + 1)) := rfl

theorem cell_congr' {t : Nat} {p q : Int} (h : p = q) : cell t p = cell t q := h ▸ rfl

/-- Left reconstruction at the named columns. -/
theorem rec_m1 (t : Nat) : cell t (-1) = xor (cell (t + 1) 0) (cell t 0 || cell t 1) := by
  have := cell_left t 0; simpa using this
theorem rec_m2 (t : Nat) : cell t (-2) = xor (cell (t + 1) (-1)) (cell t (-1) || cell t 0) := by
  have := cell_left t (-1)
  rw [cell_congr' (show (-1 : Int) - 1 = -2 by rfl), cell_congr' (show (-1 : Int) + 1 = 0 by rfl)] at this
  exact this
theorem rec_m3 (t : Nat) : cell t (-3) = xor (cell (t + 1) (-2)) (cell t (-2) || cell t (-1)) := by
  have := cell_left t (-2)
  rw [cell_congr' (show (-2 : Int) - 1 = -3 by rfl), cell_congr' (show (-2 : Int) + 1 = -1 by rfl)] at this
  exact this
theorem rec_m4 (t : Nat) : cell t (-4) = xor (cell (t + 1) (-3)) (cell t (-3) || cell t (-2)) := by
  have := cell_left t (-3)
  rw [cell_congr' (show (-3 : Int) - 1 = -4 by rfl), cell_congr' (show (-3 : Int) + 1 = -2 by rfl)] at this
  exact this
theorem step_c1 (t : Nat) : cell (t + 1) 1 = xor (cell t 0) (cell t 1 || cell t 2) := by
  rw [step_eq]; rfl

/-- The center column alternates from `T`: white at even offsets, black at odd offsets. -/
def Alt (T : Nat) : Prop := ∀ k : Nat, cell (T + 2 * k) 0 = false ∧ cell (T + 2 * k + 1) 0 = true

section
variable {T : Nat} (h : Alt T)
include h

theorem alt_left_one (k : Nat) : cell (T + 2 * k + 1) (-1) = true := by
  rw [rec_m1, (h k).2, show T + 2 * k + 1 + 1 = T + 2 * (k + 1) by omega, (h (k + 1)).1]; rfl

theorem alt_right_even (k : Nat) : cell (T + 2 * k) 1 = !cell (T + 2 * k) (-1) := by
  rw [rec_m1, (h k).1, show T + 2 * k + 1 = T + 2 * k + 1 from rfl, (h k).2]
  cases cell (T + 2 * k) 1 <;> rfl

theorem alt_golden (k : Nat) (hz : cell (T + 2 * k) (-1) = false) : cell (T + 2 * k + 2) (-1) = true := by
  have h1 : cell (T + 2 * k) 1 = true := by rw [alt_right_even h k, hz]; rfl
  have h2 : cell (T + 2 * k + 1) 1 = true := by rw [step_c1, (h k).1, h1]; rfl
  have h3 : cell (T + 2 * (k + 1)) 1 = false := by
    rw [show T + 2 * (k + 1) = (T + 2 * k + 1) + 1 by omega, step_c1, (h k).2, h2]; rfl
  rw [show T + 2 * k + 2 = T + 2 * (k + 1) by omega, rec_m1, (h (k + 1)).1, h3, (h (k + 1)).2]; rfl

theorem alt_col2_even (k : Nat) : cell (T + 2 * k) (-2) = !cell (T + 2 * k) (-1) := by
  rw [rec_m2, alt_left_one h k, (h k).1]; cases cell (T + 2 * k) (-1) <;> rfl

theorem alt_col2_odd (k : Nat) : cell (T + 2 * k + 1) (-2) = !cell (T + 2 * k + 2) (-1) := by
  rw [rec_m2, alt_left_one h k, show T + 2 * k + 1 + 1 = T + 2 * k + 2 by omega]
  cases cell (T + 2 * k + 2) (-1) <;> rfl

theorem alt_col3_even (k : Nat) : cell (T + 2 * k) (-3) = cell (T + 2 * k + 2) (-1) := by
  rw [rec_m3, alt_col2_odd h k, alt_col2_even h k]
  cases cell (T + 2 * k + 2) (-1) <;> cases cell (T + 2 * k) (-1) <;> rfl

theorem alt_col3_odd (k : Nat) : cell (T + 2 * k + 1) (-3) = cell (T + 2 * k + 2) (-1) := by
  rw [rec_m3, show T + 2 * k + 1 + 1 = T + 2 * (k + 1) by omega, alt_col2_even h (k + 1),
    alt_col2_odd h k, alt_left_one h k, show T + 2 * (k + 1) = T + 2 * k + 2 by omega]
  cases cell (T + 2 * k + 2) (-1) <;> rfl

theorem alt_col4_even (k : Nat) : cell (T + 2 * k) (-4) = false := by
  rw [rec_m4, alt_col3_odd h k, alt_col3_even h k, alt_col2_even h k]
  cases ha : cell (T + 2 * k + 2) (-1) with
  | true => cases cell (T + 2 * k) (-1) <;> rfl
  | false =>
    cases hb : cell (T + 2 * k) (-1) with
    | false => exact absurd (alt_golden h k hb) (by rw [ha]; decide)
    | true => rfl

end

end R30NewIdeas
