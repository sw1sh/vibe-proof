import Ruliology.CellularAutomata.Rule30Jen

/-!
# Barrier B6: no finite automaton reading from the edge gives a ranking function

Self-contained (repeats the ZBL definitions of `ZBLBarrier.lean`).

A DFA `A` (states: natural numbers below `N`, start state `0`) reads a finite left configuration of
width `W` from its edge: depths `W, W-1, ..., 1`. `maxAcc` is the length of the longest accepted prefix
(`-1` if none). `CertE A` says this quantity strictly decreases along every surviving double step of every
finite start. `no_edge_dfa_ranking`: no such DFA exists, whatever its number of states.

Proof idea: along the run of the truncated stripe `trunc n`, after `j` double steps the configuration read
from the edge is `Z_j ++ (01)^k` with `Z_j` independent of `n` and `k = (n+1-2j)/2`. Reading `(01)^k` the
automaton enters a cycle; if the cycle accepts, the ranking is at least `n + 2j - O(1)` (too large: it must be
at most `n - j`); otherwise it is at most `4j + O(1)` (too small: the run survives `(n-1)/2 - j` more steps).
-/

namespace ZBLEdgeDFA

def z (s : Nat → Bool) : Nat → Nat → Bool
  | 0, k => if k = 0 then false else s k
  | t + 1, k => if k = 0 then false else xor (z s t (k + 1)) (z s t k || z s t (k - 1))

theorem z_wall (s : Nat → Bool) (t : Nat) : z s t 0 = false := by cases t <;> simp [z]
theorem z_zero {s : Nat → Bool} {k : Nat} (hk : k ≠ 0) : z s 0 k = s k := by simp [z, hk]
theorem z_succ {s : Nat → Bool} {t k : Nat} (hk : k ≠ 0) :
    z s (t + 1) k = xor (z s t (k + 1)) (z s t k || z s t (k - 1)) := by simp [z, hk]

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

def trunc (n : Nat) (k : Nat) : Bool := stripe k && decide (k ≤ n)

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

def iter (s : Nat → Bool) (j : Nat) : Nat → Bool := fun k => z s (2 * j) k
def Survives (s : Nat → Bool) : Prop := z s 0 1 = true ∧ z s 2 1 = true

theorem iter_survives {n : Nat} (hn : n % 2 = 1) {j : Nat} (hj : 2 * j + 2 ≤ n) :
    Survives (iter (trunc n) j) := by
  unfold Survives iter
  rw [z_restart, z_restart]
  refine ⟨?_, ?_⟩
  · rw [trunc_agree hn _ 1 (by omega)]; rfl
  · rw [trunc_agree hn _ 1 (by omega)]; rfl

theorem iter_succ (s : Nat → Bool) (j : Nat) : (fun k => z (iter s j) 2 k) = iter s (j + 1) := by
  funext k
  unfold iter
  rw [z_restart, show 2 * j + 2 = 2 * (j + 1) by omega]

/-! ## Automata -/

structure DFA where
  δ : Nat → Bool → Nat
  F : Nat → Bool

def run (A : DFA) : Nat → List Bool → Nat
  | q, [] => q
  | q, b :: w => run A (A.δ q b) w

def maxAcc (A : DFA) : Nat → List Bool → Int
  | q, [] => if A.F q then 0 else -1
  | q, b :: w => if 0 ≤ maxAcc A (A.δ q b) w then maxAcc A (A.δ q b) w + 1 else (if A.F q then 0 else -1)

theorem run_append (A : DFA) : ∀ (q : Nat) (u v : List Bool), run A q (u ++ v) = run A (run A q u) v
  | q, [], v => rfl
  | q, b :: u, v => run_append A (A.δ q b) u v

theorem maxAcc_nil (A : DFA) (q : Nat) : maxAcc A q [] = if A.F q then 0 else -1 := rfl
theorem maxAcc_cons (A : DFA) (q : Nat) (b : Bool) (w : List Bool) :
    maxAcc A q (b :: w) = if 0 ≤ maxAcc A (A.δ q b) w then maxAcc A (A.δ q b) w + 1
      else (if A.F q then 0 else -1) := rfl

theorem maxAcc_ge (A : DFA) : ∀ (q : Nat) (w : List Bool), -1 ≤ maxAcc A q w
  | q, [] => by rw [maxAcc_nil]; split <;> omega
  | q, b :: w => by
    rw [maxAcc_cons]
    have := maxAcc_ge A (A.δ q b) w
    split
    · omega
    · split <;> omega

theorem maxAcc_le (A : DFA) : ∀ (q : Nat) (w : List Bool), maxAcc A q w ≤ w.length
  | q, [] => by rw [maxAcc_nil]; split <;> simp
  | q, b :: w => by
    rw [maxAcc_cons]
    have := maxAcc_le A (A.δ q b) w
    simp only [List.length_cons]
    split
    · omega
    · split <;> omega

theorem maxAcc_neg (A : DFA) (q : Nat) (w : List Bool) (h : maxAcc A q w < 0) :
    A.F q = false ∧ maxAcc A q w = -1 := by
  cases w with
  | nil =>
    rw [maxAcc_nil] at h ⊢
    cases hq : A.F q <;> simp_all
  | cons b w =>
    rw [maxAcc_cons] at h ⊢
    have := maxAcc_ge A (A.δ q b) w
    by_cases hr : 0 ≤ maxAcc A (A.δ q b) w
    · simp only [hr, if_true] at h; omega
    · simp only [hr, if_false] at h ⊢
      cases hq : A.F q <;> simp_all

theorem maxAcc_append (A : DFA) : ∀ (q : Nat) (u v : List Bool),
    maxAcc A q (u ++ v) = if 0 ≤ maxAcc A (run A q u) v then (u.length : Int) + maxAcc A (run A q u) v
      else maxAcc A q u
  | q, [], v => by
    simp only [List.nil_append, run, List.length_nil]
    by_cases h : 0 ≤ maxAcc A q v
    · simp [h]
    · simp only [h, if_false]
      have := maxAcc_neg A q v (by omega)
      rw [this.2, maxAcc_nil, this.1]; rfl
  | q, b :: u, v => by
    simp only [List.cons_append, run, List.length_cons]
    rw [maxAcc_cons, maxAcc_append A (A.δ q b) u v, maxAcc_cons]
    by_cases h : 0 ≤ maxAcc A (run A (A.δ q b) u) v
    · have : 0 ≤ (u.length : Int) + maxAcc A (run A (A.δ q b) u) v := by omega
      simp only [h, if_true, this]
      push_cast
      omega
    · simp only [h, if_false]

/-- If the state after reading `u` accepts, the longest accepted prefix of `u ++ v` has length at least `|u|`. -/
theorem maxAcc_ge_of_acc (A : DFA) (q : Nat) (u v : List Bool) (h : A.F (run A q u) = true) :
    (u.length : Int) ≤ maxAcc A q (u ++ v) := by
  have key : ∀ (q : Nat) (u : List Bool), A.F (run A q u) = true → (u.length : Int) ≤ maxAcc A q u := by
    intro q u
    induction u generalizing q with
    | nil => intro h; simp only [run] at h; rw [maxAcc_nil, h]; simp
    | cons b u ih =>
      intro h
      simp only [run] at h
      have := ih (A.δ q b) h
      rw [maxAcc_cons]
      simp only [List.length_cons]
      have h0 : 0 ≤ maxAcc A (A.δ q b) u := by omega
      simp only [h0, if_true]
      push_cast
      omega
  rw [maxAcc_append]
  by_cases h' : 0 ≤ maxAcc A (run A q u) v
  · simp only [h', if_true]; omega
  · simp only [h', if_false]; exact key q u h

/-! ## Reading `(01)^k` -/

def alt : Nat → List Bool
  | 0 => []
  | k + 1 => false :: true :: alt k

theorem alt_length (k : Nat) : (alt k).length = 2 * k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [alt, ih]; omega

theorem alt_add : ∀ a b, alt (a + b) = alt a ++ alt b
  | 0, b => by simp [alt]
  | a + 1, b => by
    rw [show a + 1 + b = (a + b) + 1 by omega]
    simp [alt, alt_add a b]

def pairStep (A : DFA) (q : Nat) : Nat := A.δ (A.δ q false) true

def iterP (A : DFA) : Nat → Nat → Nat
  | 0, q => q
  | k + 1, q => iterP A k (pairStep A q)

theorem iterP_add (A : DFA) : ∀ a b q, iterP A (a + b) q = iterP A b (iterP A a q)
  | 0, b, q => by simp [iterP]
  | a + 1, b, q => by
    rw [show a + 1 + b = (a + b) + 1 by omega]
    simp only [iterP]
    exact iterP_add A a b (pairStep A q)

theorem run_alt (A : DFA) : ∀ k q, run A q (alt k) = iterP A k q
  | 0, q => rfl
  | k + 1, q => by simp only [alt, run, iterP]; exact run_alt A k _

/-- No acceptance from some point on: the longest accepted prefix of `(01)^k` is short. -/
theorem maxAcc_alt_dead (A : DFA) (q : Nat)
    (hdead : ∀ i, A.F (iterP A i q) = false ∧ A.F (A.δ (iterP A i q) false) = false) :
    ∀ k, maxAcc A q (alt k) = -1 := by
  intro k
  induction k generalizing q with
  | zero =>
    have h0 := (hdead 0).1
    simp only [iterP] at h0
    rw [show alt 0 = [] from rfl, maxAcc_nil, h0]; rfl
  | succ k ih =>
    have hq : ∀ i, A.F (iterP A i (pairStep A q)) = false ∧ A.F (A.δ (iterP A i (pairStep A q)) false) = false :=
      fun i => hdead (i + 1)
    have h1 := ih (pairStep A q) hq
    have hf0 := (hdead 0).1
    have hf1 := (hdead 0).2
    simp only [iterP] at hf0 hf1
    rw [show alt (k + 1) = false :: true :: alt k from rfl, maxAcc_cons, maxAcc_cons]
    simp only [pairStep] at h1
    rw [h1]
    simp [hf0, hf1]

/-! ## The edge word of the truncated-stripe run -/

def edgeWord (s : Nat → Bool) (W : Nat) : List Bool := (List.range W).map fun i => s (W - i)

def CertE (A : DFA) : Prop :=
  ∀ (s : Nat → Bool) (W : Nat), 1 ≤ W → s W = true → (∀ k, W < k → s k = false) → Survives s →
    maxAcc A 0 (edgeWord (fun k => z s 2 k) (W + 2)) < maxAcc A 0 (edgeWord s W)

theorem trunc_width {n : Nat} (hn : n % 2 = 1) : trunc n n = true ∧ ∀ k, n < k → trunc n k = false := by
  refine ⟨?_, fun k hk => ?_⟩
  · simp [trunc, stripe, hn]
  · simp [trunc]; omega

/-- Chain of decreases along the truncated-stripe run. -/
theorem chain {A : DFA} (hA : CertE A) {n : Nat} (hn : n % 2 = 1) :
    ∀ j d, 2 * (j + d) ≤ n - 1 →
      maxAcc A 0 (edgeWord (iter (trunc n) (j + d)) (n + 2 * (j + d))) + d ≤
        maxAcc A 0 (edgeWord (iter (trunc n) j) (n + 2 * j)) := by
  intro j d
  induction d with
  | zero => intro _; simp
  | succ d ih =>
    intro hd
    have ih' := ih (by omega)
    have hw := z_width (s := trunc n) (W := n) (by omega) (trunc_width hn).1 (trunc_width hn).2 (2 * (j + d))
    have hstep := hA (iter (trunc n) (j + d)) (n + 2 * (j + d)) (by omega) hw.1 hw.2 (iter_survives hn (by omega))
    rw [iter_succ, show n + 2 * (j + d) + 2 = n + 2 * (j + (d + 1)) by omega,
      show j + d + 1 = j + (d + 1) by omega] at hstep
    push_cast
    omega

theorem range_add_map (a b : Nat) (f : Nat → Bool) :
    (List.range (a + b)).map f = (List.range a).map f ++ (List.range b).map (fun i => f (a + i)) := by
  rw [List.range_add, List.map_append, List.map_map]
  rfl

theorem stripe_part (n j : Nat) (hn : n % 2 = 1) (hj : 2 * j ≤ n + 1) :
    (List.range (n + 1 - 2 * j)).map (fun i => stripe (n + 1 - 2 * j - i)) = alt ((n + 1 - 2 * j) / 2) := by
  have key : ∀ k, (List.range (2 * k)).map (fun i => stripe (2 * k - i)) = alt k := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [show 2 * (k + 1) = 2 + 2 * k by omega, range_add_map]
      have h1 : (List.range 2).map (fun i => stripe (2 + 2 * k - i)) = [false, true] := by
        simp [List.range, List.range.loop, stripe]
      rw [h1]
      have h2 : (List.range (2 * k)).map (fun i => stripe (2 + 2 * k - (2 + i))) =
          (List.range (2 * k)).map (fun i => stripe (2 * k - i)) := by
        apply List.map_congr_left; intro i _; congr 1; omega
      rw [h2, ih]; rfl
  have he : n + 1 - 2 * j = 2 * ((n + 1 - 2 * j) / 2) := by omega
  rw [he, key, ← he]

theorem edge_split {n : Nat} (hn : n % 2 = 1) (j : Nat) (hj1 : 1 ≤ j) (hj : 4 * j ≤ n) :
    edgeWord (iter (trunc n) j) (n + 2 * j) =
      (List.range (4 * j - 1)).map (fun i => z (trunc n) (2 * j) (n + 2 * j - i)) ++ alt ((n + 1 - 2 * j) / 2) := by
  unfold edgeWord iter
  rw [show n + 2 * j = (4 * j - 1) + (n + 1 - 2 * j) by omega, range_add_map,
    ← show n + 2 * j = (4 * j - 1) + (n + 1 - 2 * j) by omega]
  congr 1
  rw [← stripe_part n j hn (by omega)]
  apply List.map_congr_left
  intro i hi
  have hi' := List.mem_range.1 hi
  rw [show n + 2 * j - (4 * j - 1 + i) = n + 1 - 2 * j - i by omega]
  exact trunc_agree hn _ _ (by omega)

theorem Z_shift (n0 m j : Nat) (hj : 4 * j ≤ n0) :
    (List.range (4 * j - 1)).map (fun i => z (trunc (n0 + 2 * m)) (2 * j) (n0 + 2 * m + 2 * j - i)) =
      (List.range (4 * j - 1)).map (fun i => z (trunc n0) (2 * j) (n0 + 2 * j - i)) := by
  apply List.map_congr_left
  intro i hi
  have hi' := List.mem_range.1 hi
  rw [show n0 + 2 * m + 2 * j - i = (n0 + 2 * j - i) + 2 * m by omega]
  exact z_shift (s := trunc n0) (s' := trunc (n0 + 2 * m)) (d := 2 * m) (a := 1) (by omega)
    (fun k _ => trunc_shift n0 m k) (2 * j) (n0 + 2 * j - i) (by omega)

/-- One-hot encoding (for the list pigeonhole principle). -/
def oneHot (N v : Nat) : List Bool := (List.range N).map fun k => k == v

theorem oneHot_inj {N v w : Nat} (hv : v < N) (h : oneHot N v = oneHot N w) : v = w := by
  have : (oneHot N v)[v]? = (oneHot N w)[v]? := by rw [h]
  simp [oneHot, hv] at this
  omega

theorem last_index (k i π : Nat) (hπ : 1 ≤ π) (hik : i + 1 ≤ k) :
    ∃ t, i + t * π ≤ k - 1 ∧ k - 1 < i + t * π + π := by
  refine ⟨(k - 1 - i) / π, ?_, ?_⟩
  · have := Nat.div_mul_le_self (k - 1 - i) π; omega
  · have := Nat.lt_div_mul_add (a := k - 1 - i) (b := π) (by omega); omega

/-- **B6.** No DFA reading the configuration from its edge defines a ranking function. -/
theorem no_edge_dfa_ranking (A : DFA) (N : Nat) (hN : 0 < N) (hδ : ∀ q b, A.δ q b < N) : ¬ CertE A := by
  intro hA
  let B := 2 ^ N
  have hB : 1 ≤ B := Nat.one_le_two_pow
  let j := B + 1
  let n0 := 4 * j + 1
  have hn0 : n0 % 2 = 1 := by omega
  let Zw := (List.range (4 * j - 1)).map (fun i => z (trunc n0) (2 * j) (n0 + 2 * j - i))
  have hZlen : Zw.length = 4 * j - 1 := by simp [Zw]
  let q := run A 0 Zw
  have hq : q < N := by
    show run A 0 Zw < N
    have : ∀ (p : Nat) (w : List Bool), p < N → run A p w < N := by
      intro p w
      induction w generalizing p with
      | nil => intro h; exact h
      | cons b w ih => intro _; exact ih _ (hδ p b)
    exact this 0 Zw hN
  have hiter : ∀ i, iterP A i q < N := by
    intro i
    induction i with
    | zero => exact hq
    | succ i ih =>
      rw [show i + 1 = i + 1 from rfl, iterP_add A i 1]
      exact hδ _ _
  obtain ⟨i1, i2, hlt, hle, heq⟩ := Ruliology.CellularAutomata.Rule30Jen.pigeonhole N
    (fun i => oneHot N (iterP A i q)) (fun i => by simp [oneHot])
  have hcyc : iterP A i1 q = iterP A i2 q := oneHot_inj (hiter i1) heq
  let π := i2 - i1
  have hper : ∀ t r, iterP A (i1 + t * π + r) q = iterP A (i1 + r) q := by
    intro t
    induction t with
    | zero => intro r; simp
    | succ t ih =>
      intro r
      rw [show i1 + (t + 1) * π + r = i2 + (t * π + r) by rw [Nat.succ_mul]; omega, iterP_add A i2,
        ← hcyc, ← iterP_add A i1, show i1 + (t * π + r) = i1 + t * π + r by omega, ih]
  -- the large truncated stripe
  let m := 10 * j + 4 * B + 10
  let n := n0 + 2 * m
  have hn : n % 2 = 1 := by omega
  let k := (n + 1 - 2 * j) / 2
  have hj_def : j = B + 1 := rfl
  have hn0_def : n0 = 4 * j + 1 := rfl
  have hm_def : m = 10 * j + 4 * B + 10 := rfl
  have hn_def : n = n0 + 2 * m := rfl
  have hB_def : B = 2 ^ N := rfl
  have hk2 : 2 * k = n + 1 - 2 * j := by omega
  have hsplit : edgeWord (iter (trunc n) j) (n + 2 * j) = Zw ++ alt k := by
    rw [edge_split hn j (by omega) (by omega)]
    congr 1
    exact Z_shift n0 m j (by omega)
  -- upper bound: decreases from time 0
  have hup : maxAcc A 0 (edgeWord (iter (trunc n) j) (n + 2 * j)) + j ≤ n := by
    have h := chain hA hn 0 j (by omega)
    simp only [Nat.zero_add, Nat.mul_zero, Nat.add_zero] at h
    have hl := maxAcc_le A 0 (edgeWord (iter (trunc n) 0) n)
    have hlen : (edgeWord (iter (trunc n) 0) n).length = n := by simp [edgeWord]
    rw [hlen] at hl
    omega
  -- lower bound: decreases until the end of the run
  have hlow : ((n - 1) / 2 - j : Nat) - 1 ≤ maxAcc A 0 (edgeWord (iter (trunc n) j) (n + 2 * j)) := by
    have h := chain hA hn j ((n - 1) / 2 - j) (by omega)
    have hg := maxAcc_ge A 0 (edgeWord (iter (trunc n) (j + ((n - 1) / 2 - j))) (n + 2 * (j + ((n - 1) / 2 - j))))
    omega
  rw [hsplit, maxAcc_append] at hup hlow
  rw [show run A 0 Zw = q from rfl] at hup hlow
  by_cases hacc : ∃ i, i1 ≤ i ∧ i < i2 ∧ (A.F (iterP A i q) = true ∨ A.F (A.δ (iterP A i q) false) = true)
  · -- case 1: an accepting state on the cycle; the ranking is too large
    obtain ⟨i, hi1, hi2, hF⟩ := hacc
    -- the last index i' ≡ i (mod π) with i' ≤ k - 1
    have hπ : 1 ≤ π := by omega
    obtain ⟨t, hi'k, hi'k2⟩ := last_index k i π hπ (by omega)
    let i' := i + t * π
    have hstate : iterP A i' q = iterP A i q := by
      have := hper t (i - i1)
      rw [show i1 + t * π + (i - i1) = i' by omega, show i1 + (i - i1) = i by omega] at this
      exact this
    have hlow' : (2 * i' : Int) ≤ maxAcc A q (alt k) := by
      have hsp : alt k = alt i' ++ (false :: true :: alt (k - 1 - i')) := by
        have hh : alt (i' + (k - 1 - i' + 1)) = alt i' ++ (false :: true :: alt (k - 1 - i')) := alt_add _ _
        rw [show i' + (k - 1 - i' + 1) = k by omega] at hh
        exact hh
      rcases hF with hF | hF
      · rw [hsp]
        have := maxAcc_ge_of_acc A q (alt i') (false :: true :: alt (k - 1 - i'))
          (by rw [run_alt, hstate]; exact hF)
        rw [alt_length] at this
        push_cast at this ⊢
        omega
      · rw [hsp, show alt i' ++ (false :: true :: alt (k - 1 - i')) =
          (alt i' ++ [false]) ++ (true :: alt (k - 1 - i')) by simp]
        have := maxAcc_ge_of_acc A q (alt i' ++ [false]) (true :: alt (k - 1 - i'))
          (by rw [run_append, run_alt, hstate]; exact hF)
        simp only [List.length_append, alt_length, List.length_singleton] at this
        push_cast at this ⊢
        omega
    have h0 : 0 ≤ maxAcc A q (alt k) := by omega
    simp only [h0, if_true, hZlen] at hup
    have : (j : Int) * 3 ≤ 2 * B + 1 := by
      push_cast at hup
      omega
    omega
  · -- case 2: no accepting state on the cycle; the ranking is too small
    have hdead : ∀ i, A.F (iterP A (i1 + i) q) = false ∧ A.F (A.δ (iterP A (i1 + i) q) false) = false := by
      intro i
      have hr := hper (i / π) (i % π)
      have hπ : 1 ≤ π := by omega
      rw [show i1 + i / π * π + i % π = i1 + i by
        have := Nat.div_add_mod i π
        rw [Nat.mul_comm] at this
        omega] at hr
      rw [hr]
      have hm : i % π < π := Nat.mod_lt _ (by omega)
      constructor
      · cases h : A.F (iterP A (i1 + i % π) q)
        · rfl
        · exact absurd ⟨i1 + i % π, by omega, by omega, Or.inl h⟩ hacc
      · cases h : A.F (A.δ (iterP A (i1 + i % π) q) false)
        · rfl
        · exact absurd ⟨i1 + i % π, by omega, by omega, Or.inr h⟩ hacc
    have hsp : alt k = alt i1 ++ alt (k - i1) := by rw [← alt_add]; congr 1; omega
    have hdead' : maxAcc A (iterP A i1 q) (alt (k - i1)) = -1 := by
      apply maxAcc_alt_dead
      intro i
      rw [← iterP_add]
      rw [show i1 + i = i1 + i from rfl]
      exact hdead i
    have hsmall : maxAcc A q (alt k) ≤ 2 * i1 := by
      rw [hsp, maxAcc_append, run_alt, hdead']
      simp only [show ¬ ((0 : Int) ≤ -1) by omega, if_false]
      have := maxAcc_le A q (alt i1)
      rw [alt_length] at this
      push_cast at this ⊢
      omega
    have hZ := maxAcc_le A 0 Zw
    rw [hZlen] at hZ
    have hi1B : i1 ≤ B := by omega
    by_cases h0 : 0 ≤ maxAcc A q (alt k)
    · simp only [h0, if_true, hZlen] at hlow
      push_cast at hlow
      omega
    · simp only [h0, if_false] at hlow
      push_cast at hlow
      omega

end ZBLEdgeDFA

-- writeup-r2 axiom audit (appended)
#print axioms ZBLEdgeDFA.no_edge_dfa_ranking
