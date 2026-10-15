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

namespace R30Skel
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

end R30Skel

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

namespace R30Skel
open Ruliology.CellularAutomata.Rule30Jen

-- bad-class certificate for w = 0011, strip width b = 3; generated by skel_export.py
def k0011_w : List Bool := [false, false, true, true]
def k0011_b : Nat := 3
def k0011_nranks : Nat := 13
def k0011_bad : Nat := 0
def k0011_rankP : Nat := 1636695304138607345681430566450342879541164928147624093384226552632404513874232764790848370478092089357155105678346690372348660919069330654870135373832
def k0011_posP : Nat := 0
def k0011_perP : Nat := 79538861190790864407636279553
def k0011_wordP : Nat := 0

def K0011 : Cert := { w := k0011_w, b := k0011_b, nranks := k0011_nranks, rankP := k0011_rankP, posP := k0011_posP, perP := k0011_perP, wordP := k0011_wordP }

/-- Skeleton predicate for `w = 0011` (phases 0..3 = 0,0,1,1): column 1 is black at phases 1, 2 and white at
phase 3. -/
def skel0011 (φ : Nat) (s : List Bool) : Bool :=
  if φ = 1 then s.getD 0 false else if φ = 2 then s.getD 0 false else if φ = 3 then !(s.getD 0 false) else true

theorem K0011_checkb : K0011.checkb k0011_bad = true := by decide +kernel
theorem K0011_checkGb : K0011.checkGb k0011_bad = true := by decide +kernel
theorem K0011_badImp : K0011.badImp k0011_bad skel0011 = true := by decide +kernel

/-- **Skeleton for `0011`.** If the center column is `0011`-periodic from time `T` (phase `(t-T) % 4`),
then eventually column 1 is black at phases 1, 2 and white at phase 3. -/
theorem skeleton_0011 (T : Nat) (h : ∀ t, T ≤ t → cell t 0 = K0011.wAt ((t - T) % 4)) :
    ∃ T', T ≤ T' ∧ ∀ t, T' ≤ t →
      ((t - T) % 4 = 1 → cell t 1 = true) ∧ ((t - T) % 4 = 2 → cell t 1 = true) ∧
      ((t - T) % 4 = 3 → cell t 1 = false) := by
  have hP : K0011.P = 4 := by decide
  obtain ⟨T', hT', hp⟩ := Cert.eventually_pred K0011 k0011_bad skel0011 K0011_checkb K0011_checkGb K0011_badImp
    (by decide) (by decide) T (by rw [hP]; exact h)
  refine ⟨T', hT', fun t ht => ?_⟩
  have e := hp t ht
  rw [hP] at e
  have h0 : (rowR t K0011.b).getD 0 false = cell t 1 := rowR_getD t K0011.b 0 (by decide)
  refine ⟨fun h1 => ?_, fun h2 => ?_, fun h3 => ?_⟩
  · rw [h1] at e; simp only [skel0011] at e; simp at e; rw [← h0]; exact e
  · rw [h2] at e; simp only [skel0011] at e; simp at e; rw [← h0]; exact e
  · rw [h3] at e; simp only [skel0011] at e; simp at e; rw [← h0]; simpa using e

end R30Skel

#print axioms R30Skel.skeleton_0011

namespace R30Skel
open Ruliology.CellularAutomata.Rule30Jen

theorem col_m1 (t : Nat) : cell t (-1) = xor (cell (t + 1) 0) (cell t 0 || cell t 1) := by
  have := cell_left t 0
  rw [show (0 : Int) - 1 = -1 by rfl, show (0 : Int) + 1 = 1 by rfl] at this
  exact this

theorem phase_succ (t T : Nat) (ht : T ≤ t) : (t + 1 - T) % 4 = ((t - T) % 4 + 1) % 4 := by
  rw [show t + 1 - T = (t - T) + 1 by omega]; omega

theorem wAt_0011 (φ : Nat) (hφ : φ < 4) : K0011.wAt φ = decide (2 ≤ φ) := by
  have : φ = 0 ∨ φ = 1 ∨ φ = 2 ∨ φ = 3 := by omega
  rcases this with h | h | h | h <;> subst h <;> decide

/-- **Skeleton for `0011`, explicit form.**  If `c(t) = [ (t-T) % 4 ≥ 2 ]` for `t ≥ T`, then eventually column 1
is black at phases 1, 2 and white at phase 3, and column -1 is (= column 1, white, white, black) at phases
(0, 1, 2, 3). -/
theorem skeleton_0011_explicit (T : Nat) (h : ∀ t, T ≤ t → cell t 0 = decide (2 ≤ (t - T) % 4)) :
    ∃ T', T ≤ T' ∧ ∀ t, T' ≤ t →
      ((t - T) % 4 = 0 → cell t (-1) = cell t 1) ∧
      ((t - T) % 4 = 1 → cell t 1 = true ∧ cell t (-1) = false) ∧
      ((t - T) % 4 = 2 → cell t 1 = true ∧ cell t (-1) = false) ∧
      ((t - T) % 4 = 3 → cell t 1 = false ∧ cell t (-1) = true) := by
  have h' : ∀ t, T ≤ t → cell t 0 = K0011.wAt ((t - T) % 4) := by
    intro t ht; rw [h t ht, wAt_0011 _ (Nat.mod_lt _ (by decide))]
  obtain ⟨T', hT', hs⟩ := skeleton_0011 T h'
  refine ⟨T', hT', fun t ht => ?_⟩
  obtain ⟨s1, s2, s3⟩ := hs t ht
  have c0 := h t (by omega)
  have c1 := h (t + 1) (by omega)
  rw [phase_succ t T (by omega)] at c1
  refine ⟨fun hφ => ?_, fun hφ => ?_, fun hφ => ?_, fun hφ => ?_⟩
  · rw [col_m1, c1, c0, hφ]; cases cell t 1 <;> decide
  · have a := s1 hφ
    refine ⟨a, ?_⟩
    rw [col_m1, c1, c0, a, hφ]; decide
  · have a := s2 hφ
    refine ⟨a, ?_⟩
    rw [col_m1, c1, c0, hφ]; cases cell t 1 <;> decide
  · have a := s3 hφ
    refine ⟨a, ?_⟩
    rw [col_m1, c1, c0, hφ]; cases cell t 1 <;> decide

/-- **Column -1 for `0111` (no skeleton needed).**  If `c(t) = [ (t-T) % 4 ≥ 1 ]` for `t ≥ T`, then for all
`t ≥ T` column -1 is (= not column 1, white, white, black) at phases (0, 1, 2, 3). -/
theorem column_m1_0111 (T : Nat) (h : ∀ t, T ≤ t → cell t 0 = decide (1 ≤ (t - T) % 4)) :
    ∀ t, T ≤ t →
      ((t - T) % 4 = 0 → cell t (-1) = !cell t 1) ∧
      ((t - T) % 4 = 1 → cell t (-1) = false) ∧
      ((t - T) % 4 = 2 → cell t (-1) = false) ∧
      ((t - T) % 4 = 3 → cell t (-1) = true) := by
  intro t ht
  have c0 := h t ht
  have c1 := h (t + 1) (by omega)
  rw [phase_succ t T ht] at c1
  refine ⟨fun hφ => ?_, fun hφ => ?_, fun hφ => ?_, fun hφ => ?_⟩ <;>
    (rw [col_m1, c1, c0, hφ]; cases cell t 1 <;> decide)

end R30Skel

#print axioms R30Skel.skeleton_0011_explicit
#print axioms R30Skel.column_m1_0111

#print axioms R30Skel.column_m1_0111

#print axioms R30Skel.skeleton_0011_explicit
