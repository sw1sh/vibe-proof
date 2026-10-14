import QTilde.Slow

/-!
# The coupled recurrences

Cloitre's parity split (arXiv:2604.06237, Lemma 2.2) turns the recursion for `Q̃` into

    (RA)   a(m) = b(m − b(m − 1)) + b(m − a(m − 1)) − 1
    (RB)   b(m) = a(m + 1 − a(m)) + a(m + 1 − b(m − 1)).

Cloitre's Theorem 3.5 proves them along the arches by propagation. Here each case is read off
directly from the interleaving that defines the arch word:

* On the positive arch of level `r + 1`, both arguments land on the tapes `00 N_r 1` and `0 N_r` of
  Law 2, exactly at the machine's two heads, and RA is the shuffle identity `pre_count`
  (`RA_pos`). RB also needs the parked-head lemma (`RB_pos`).
* On the negative arch of level `r`, the same holds for the tapes `P_r[2 :]` and `P_r[: −1]` of
  Law 1 (`RB_neg`, `RA_neg`).

The tape formulas (`B_S0`, `B_S1`, `A_S0`, `A_S1`, `A_tapeX`, `A_tapeY`, `B_tapeX`, `B_tapeY`) say
that `a` and `b` read along a tape add up its letters (Cloitre's coordinate identities in the proof
of Lemma 3.4).
-/

namespace QTilde

/-! ### Letter counts -/

theorem count_false_add_true (l : List Bool) : l.count false + l.count true = l.length := by
  induction l with
  | nil => rfl
  | cons a l ih => cases a <;> simp <;> omega

theorem count_take_succ_of (l : List Bool) {k : Nat} {b : Bool} (h : l[k]? = some b) (c : Bool) :
    (l.take (k + 1)).count c = (l.take k).count c + (if b = c then 1 else 0) := by
  rw [List.take_add_one, h, Option.toList_some, List.count_append, List.count_singleton]
  cases b <;> cases c <;> rfl

theorem count_take_ff (p : Nat) (c : Bool) :
    ([false, false].take p).count c = if c then 0 else min p 2 := by
  rcases p with _ | _ | p <;> cases c <;> simp <;> omega

theorem count_take_f (q : Nat) (c : Bool) :
    ([false].take q).count c = if c then 0 else min q 1 := by
  rcases q with _ | q <;> cases c <;> simp <;> omega

theorem count_take_t (k : Nat) (c : Bool) :
    ([true].take k).count c = if c then min k 1 else 0 := by
  rcases k with _ | k <;> cases c <;> simp <;> omega

theorem count_take_tape0 (Nw : List Bool) (p : Nat) (c : Bool) :
    ((tape0 Nw).take p).count c = (if c then 0 else min p 2) + (Nw.take (p - 2)).count c +
      (if c then min (p - 2 - Nw.length) 1 else 0) := by
  rw [tape0, List.append_assoc, List.take_append, List.take_append, List.count_append,
    List.count_append, count_take_ff, count_take_t]
  simp only [List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd]
  omega

theorem count_take_tape1 (Nw : List Bool) (q : Nat) (c : Bool) :
    ((tape1 Nw).take q).count c = (if c then 0 else min q 1) + (Nw.take (q - 1)).count c := by
  rw [tape1, List.take_append, List.count_append, count_take_f]
  simp only [List.length_cons, List.length_nil, Nat.zero_add]

theorem count_take_drop2 {l : List Bool} (h0 : l[0]? = some false) (h1 : l[1]? = some false)
    (p : Nat) (c : Bool) :
    ((l.drop 2).take p).count c + (if c then 0 else 2) = (l.take (p + 2)).count c := by
  have e := eq_ff_cons h0 h1
  conv => rhs; rw [e]
  rw [show p + 2 = (p + 1) + 1 by omega, List.take_succ_cons, List.take_succ_cons]
  cases c <;> simp <;> omega

theorem take_dropLast_eq {l : List Bool} {q : Nat} (hq : q ≤ l.dropLast.length) :
    l.dropLast.take q = l.take q := by
  rw [List.dropLast_eq_take, List.take_take]
  congr 1
  simp at hq
  omega

/-- The counts at the end of a positive arch word, which ends in `11`. -/
theorem P_counts_end (r : Nat) :
    ((P r).take (2 * ar r - 1)).count true = ar r - 1 ∧
    ((P r).take (2 * ar r - 1)).count false = ar r ∧
    ((P r).take (2 * ar r - 2)).count false = ar r ∧
    ((P r).take (2 * ar r - 2)).count true = ar r - 2 := by
  have F := archFacts r
  have ha := ar_ge r
  have hfull : (P r).take (2 * ar r) = P r := by rw [← lenP]; exact List.take_length
  have e1 := count_take_succ_of (P r) (k := 2 * ar r - 1) F.Plast
  have e2 := count_take_succ_of (P r) (k := 2 * ar r - 2) F.Plast2
  rw [show 2 * ar r - 1 + 1 = 2 * ar r by omega, hfull] at e1
  rw [show 2 * ar r - 2 + 1 = 2 * ar r - 1 by omega] at e2
  have t1 := e1 true; have f1 := e1 false; have t2 := e2 true; have f2 := e2 false
  simp only [↓reduceIte, Bool.true_eq_false] at t1 f1 t2 f2
  rw [F.onesP] at t1; rw [F.zerosP] at f1
  refine ⟨by omega, by omega, by omega, by omega⟩

/-! ### Tape formulas -/

theorem A_tapeX (r p : Nat) (hp : p ≤ ((P r).drop 2).length) :
    A (u r + 2 + p) = ar r + (((P r).drop 2).take p).count true := by
  have h := count_take_drop2 (archFacts r).P0 (archFacts r).P1 p true
  rw [if_pos rfl, Nat.add_zero] at h
  have hl := lenP r; have := ar_ge r
  simp only [List.length_drop] at hp
  rw [show u r + 2 + p = u r + (p + 2) by omega, A_pos r (p + 2) (by omega), h]

theorem B_tapeX (r p : Nat) (hp : p ≤ ((P r).drop 2).length) :
    B (u r + 2 + p) = ar r + 2 + (((P r).drop 2).take p).count false := by
  have h := count_take_drop2 (archFacts r).P0 (archFacts r).P1 p false
  rw [if_neg (by decide)] at h
  have hl := lenP r; have := ar_ge r
  simp only [List.length_drop] at hp
  rw [show u r + 2 + p = u r + (p + 2) by omega, B_pos r (p + 2) (by omega), ← h]
  omega

theorem A_tapeY (r q : Nat) (hq : q ≤ (P r).dropLast.length) :
    A (u r + q) = ar r + ((P r).dropLast.take q).count true := by
  have hl := lenP r
  rw [take_dropLast_eq hq, A_pos r q (by simp at hq; omega)]

theorem B_tapeY (r q : Nat) (hq : q ≤ (P r).dropLast.length) :
    B (u r + q) = ar r + ((P r).dropLast.take q).count false := by
  have hl := lenP r
  rw [take_dropLast_eq hq, B_pos r q (by simp at hq; omega)]

/-- The second letter of each positive arch word is a zero, so `a` stays put at its start. -/
theorem A_u_one (r : Nat) : A (u r + 1) = ar r := by
  have h := count_take_succ_of (P r) (k := 0) (archFacts r).P0 true
  rw [Nat.zero_add, List.take_zero, List.count_nil, if_neg (by decide)] at h
  rw [A_pos r 1 (by have := ar_ge r; omega), h]
  omega

theorem A_u_two (r : Nat) : A (u r + 2) = ar r := by
  have h0 := count_take_succ_of (P r) (k := 0) (archFacts r).P0 true
  have h1 := count_take_succ_of (P r) (k := 1) (archFacts r).P1 true
  rw [Nat.zero_add, List.take_zero, List.count_nil, if_neg (by decide)] at h0
  rw [if_neg (by decide), h0] at h1
  rw [A_pos r 2 (by have := ar_ge r; omega), h1]
  omega

theorem B_u_one (r : Nat) : B (u r + 1) = ar r + 1 := by
  have h := count_take_succ_of (P r) (k := 0) (archFacts r).P0 false
  rw [Nat.zero_add, List.take_zero, List.count_nil, if_pos rfl] at h
  rw [B_pos r 1 (by have := ar_ge r; omega), h]

theorem B_S0 (r p : Nat) (hp : p ≤ (tape0 (N r)).length) :
    B (v r - 2 + p) = 2 * ar r + ((tape0 (N r)).take p).count true := by
  have ha := ar_ge r; have hN := lenN r; have hve := v_eq r; have hus := u_succ r
  have hu := u_ge r
  have E := P_counts_end r
  have hl0 : (tape0 (N r)).length = (N r).length + 3 := by simp [tape0] <;> omega
  rw [count_take_tape0]
  simp only [↓reduceIte]
  rcases (show p ≤ 1 ∨ (2 ≤ p ∧ p ≤ (N r).length + 2) ∨ p = (N r).length + 3 by omega) with
    h | ⟨h1, h2⟩ | h
  · rw [show v r - 2 + p = u r + (2 * ar r - 2 + p) by omega, B_pos r _ (by omega),
      show p - 2 = 0 by omega, List.take_zero, List.count_nil]
    rcases (show p = 0 ∨ p = 1 by omega) with rfl | rfl
    · rw [Nat.add_zero, E.2.2.1]; omega
    · rw [show 2 * ar r - 2 + 1 = 2 * ar r - 1 by omega, E.2.1]; omega
  · rw [show v r - 2 + p = v r + (p - 2) by omega, B_neg r (p - 2) (by omega)]
    omega
  · subst h
    rw [show v r - 2 + ((N r).length + 3) = u (r + 1) + 1 by omega, B_u_one, ar_succ,
      show (N r).length + 3 - 2 = (N r).length + 1 by omega,
      List.take_of_length_le (show (N r).length ≤ (N r).length + 1 by omega), (archFacts r).onesN]
    omega

theorem B_S1 (r q : Nat) (hq : q ≤ (tape1 (N r)).length) :
    B (v r - 1 + q) = 2 * ar r + ((tape1 (N r)).take q).count true := by
  have ha := ar_ge r; have hN := lenN r; have hve := v_eq r; have hus := u_succ r
  have hu := u_ge r
  have E := P_counts_end r
  have hl1 : (tape1 (N r)).length = (N r).length + 1 := by simp [tape1] <;> omega
  rw [count_take_tape1]
  simp only [↓reduceIte]
  rcases Nat.eq_zero_or_pos q with rfl | h
  · rw [show v r - 1 + 0 = u r + (2 * ar r - 1) by omega, B_pos r _ (by omega), E.2.1,
      Nat.zero_sub, List.take_zero, List.count_nil]
    omega
  · rw [show v r - 1 + q = v r + (q - 1) by omega, B_neg r (q - 1) (by omega)]
    omega

theorem A_S0 (r p : Nat) (hp : p ≤ (tape0 (N r)).length) :
    A (v r - 1 + p) + 1 = 2 * ar r + ((tape0 (N r)).take p).count false := by
  have ha := ar_ge r; have hN := lenN r; have hve := v_eq r; have hus := u_succ r
  have hu := u_ge r
  have E := P_counts_end r
  have hl0 : (tape0 (N r)).length = (N r).length + 3 := by simp [tape0] <;> omega
  rw [count_take_tape0]
  simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
  rcases (show p = 0 ∨ p = 1 ∨ (2 ≤ p ∧ p ≤ (N r).length + 1) ∨ p = (N r).length + 2 ∨
      p = (N r).length + 3 by omega) with h | h | ⟨h1, h2⟩ | h | h
  · subst h
    rw [show v r - 1 + 0 = u r + (2 * ar r - 1) by omega, A_pos r _ (by omega), E.1,
      Nat.zero_sub, List.take_zero, List.count_nil]
    omega
  · subst h
    rw [show v r - 1 + 1 = v r by omega, A_v, show 1 - 2 = 0 by rfl, List.take_zero,
      List.count_nil]
    omega
  · rw [show v r - 1 + p = v r + (p - 1) by omega, A_neg r (p - 1) (by omega) (by omega),
      show p - 1 - 1 = p - 2 by omega]
    omega
  · subst h
    rw [show v r - 1 + ((N r).length + 2) = u (r + 1) + 1 by omega, A_u_one, ar_succ,
      show (N r).length + 2 - 2 = (N r).length by omega, List.take_length, (archFacts r).zerosN]
    omega
  · subst h
    rw [show v r - 1 + ((N r).length + 3) = u (r + 1) + 2 by omega, A_u_two, ar_succ,
      show (N r).length + 3 - 2 = (N r).length + 1 by omega,
      List.take_of_length_le (show (N r).length ≤ (N r).length + 1 by omega),
      (archFacts r).zerosN]
    omega

theorem A_S1 (r q : Nat) (hq : q ≤ (tape1 (N r)).length) :
    A (v r + q) = 2 * ar r + ((tape1 (N r)).take q).count false := by
  have ha := ar_ge r; have hN := lenN r; have hve := v_eq r; have hus := u_succ r
  have hu := u_ge r
  have hl1 : (tape1 (N r)).length = (N r).length + 1 := by simp [tape1] <;> omega
  rw [count_take_tape1]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rcases (show q = 0 ∨ (1 ≤ q ∧ q ≤ (N r).length) ∨ q = (N r).length + 1 by omega) with
    h | ⟨h1, h2⟩ | h
  · subst h; rw [Nat.add_zero, A_v, Nat.zero_sub, List.take_zero, List.count_nil]; omega
  · rw [A_neg r q h1 h2]; omega
  · subst h
    rw [show v r + ((N r).length + 1) = u (r + 1) + 1 by omega, A_u_one, ar_succ,
      show (N r).length + 1 - 1 = (N r).length by omega, List.take_length, (archFacts r).zerosN]
    omega

/-! ### The recurrences on the arches -/

/-- Cloitre's (RA): `a(m) = b(m − b(m − 1)) + b(m − a(m − 1)) − 1`. -/
def RA (m : Nat) : Prop := A m + 1 = B (m - B (m - 1)) + B (m - A (m - 1))

/-- Cloitre's (RB): `b(m) = a(m + 1 − a(m)) + a(m + 1 − b(m − 1))`. -/
def RB (m : Nat) : Prop := B m = A (m + 1 - A m) + A (m + 1 - B (m - 1))

/-- The positive arch word of level `r + 1` is a prefix-wise shuffle of Law 2's tapes. -/
theorem P_take_succ (r k : Nat) (hk : k ≤ 2 * ar (r + 1)) :
    (P (r + 1)).take k = pre (tape0 (N r)) (tape1 (N r)) false k := by
  have hN := lenN r; have ha := ar_ge r
  have hL : (tape0 (N r)).length + (tape1 (N r)).length = 2 * ar (r + 1) := by
    simp [tape0, tape1, hN, ar_succ]; omega
  rw [P_succ, interleave, pre_take (by omega)]

/-- The negative arch word of level `r` is a prefix-wise shuffle of Law 1's tapes. -/
theorem N_take (r k : Nat) (hk : k ≤ (N r).length) :
    (N r).take k = pre ((P r).drop 2) (P r).dropLast true k := by
  have hL : ((P r).drop 2).length + (P r).dropLast.length = (N r).length := by
    simp [N, law1]
  rw [N, law1, interleave, pre_take (by rw [N, law1, interleave_length] at hk; omega)]

theorem count_pre_pos {X Y : List Bool} {ε : Bool} (h0 : out X Y ε 0 = false) {t : Nat}
    (ht : 1 ≤ t) : 1 ≤ (pre X Y ε t).count false := by
  have hs : (pre X Y ε 1).Sublist (pre X Y ε t) := by
    rw [← pre_take ht]; exact List.take_sublist _ _
  have := hs.count_le false
  have e : (pre X Y ε 1).count false = 1 := by
    rw [show (1 : Nat) = 0 + 1 from rfl, pre_succ, pre_zero, h0]; rfl
  omega

/-- **RA on the positive arch** of level `r + 1`. -/
theorem RA_pos (r t : Nat) (ht : t + 1 ≤ 2 * ar (r + 1)) : RA (u (r + 1) + (t + 1)) := by
  have hf := (archFacts r).fits2
  have ha := ar_ge r; have hN := lenN r; have hve := v_eq r; have hus := u_succ r
  have hu := u_ge r; have ha1 := ar_succ r
  have hL : (tape0 (N r)).length + (tape1 (N r)).length = 2 * ar (r + 1) := by
    simp [tape0, tape1, hN, ar_succ]; omega
  have hi := head_i_eq (X := tape0 (N r)) (Y := tape1 (N r)) (ε := false) t
  have hj := head_j_eq (X := tape0 (N r)) (Y := tape1 (N r)) (ε := false) t
  simp only [Bool.false_eq_true, ↓reduceIte] at hi hj
  have hc := pre_count hf true (t + 1) (by omega)
  have hle := head_le_of_fits hf (t + 1) (by omega)
  have hZO := count_false_add_true (pre (tape0 (N r)) (tape1 (N r)) false t)
  rw [pre_length] at hZO
  have eB : B (u (r + 1) + (t + 1) - 1) =
      ar (r + 1) + (pre (tape0 (N r)) (tape1 (N r)) false t).count false := by
    rw [show u (r + 1) + (t + 1) - 1 = u (r + 1) + t by omega, B_pos (r + 1) t (by omega),
      P_take_succ r t (by omega)]
  have eA : A (u (r + 1) + (t + 1) - 1) =
      ar (r + 1) + (pre (tape0 (N r)) (tape1 (N r)) false t).count true := by
    rw [show u (r + 1) + (t + 1) - 1 = u (r + 1) + t by omega, A_pos (r + 1) t (by omega),
      P_take_succ r t (by omega)]
  unfold RA
  rw [eB, eA, A_pos (r + 1) (t + 1) ht, P_take_succ r (t + 1) ht,
    show u (r + 1) + (t + 1) - (ar (r + 1) + (pre (tape0 (N r)) (tape1 (N r)) false t).count false)
      = v r - 1 + (head (tape0 (N r)) (tape1 (N r)) false (t + 1)).j by omega,
    show u (r + 1) + (t + 1) - (ar (r + 1) + (pre (tape0 (N r)) (tape1 (N r)) false t).count true)
      = v r - 2 + (head (tape0 (N r)) (tape1 (N r)) false (t + 1)).i by omega,
    B_S1 r _ hle.2, B_S0 r _ hle.1]
  omega

/-- **RB on the positive arch** of level `r + 1`. -/
theorem RB_pos (r t : Nat) (ht : t + 1 ≤ 2 * ar (r + 1)) : RB (u (r + 1) + (t + 1)) := by
  have hf := (archFacts r).fits2
  have ha := ar_ge r; have hN := lenN r; have hve := v_eq r; have hus := u_succ r
  have hu := u_ge r; have ha1 := ar_succ r
  have hL : (tape0 (N r)).length + (tape1 (N r)).length = 2 * ar (r + 1) := by
    simp [tape0, tape1, hN, ar_succ]; omega
  have hi := head_i_eq (X := tape0 (N r)) (Y := tape1 (N r)) (ε := false) t
  have hj := head_j_eq (X := tape0 (N r)) (Y := tape1 (N r)) (ε := false) t
  simp only [Bool.false_eq_true, ↓reduceIte] at hi hj
  have hc := pre_count hf false (t + 1) (by omega)
  have hle := head_le_of_fits hf (t + 1) (by omega)
  have hZO := count_false_add_true (pre (tape0 (N r)) (tape1 (N r)) false t)
  rw [pre_length] at hZO
  have hZO1 := count_false_add_true (pre (tape0 (N r)) (tape1 (N r)) false (t + 1))
  rw [pre_length] at hZO1
  have hstep : ∀ c, (pre (tape0 (N r)) (tape1 (N r)) false (t + 1)).count c =
      (pre (tape0 (N r)) (tape1 (N r)) false t).count c +
        (if out (tape0 (N r)) (tape1 (N r)) false t = c then 1 else 0) := by
    intro c; rw [pre_succ, List.count_append, List.count_singleton]
    cases out (tape0 (N r)) (tape1 (N r)) false t <;> cases c <;> rfl
  -- the `X`-head, seen from the zeros emitted so far
  have key : ((tape0 (N r)).take
        ((pre (tape0 (N r)) (tape1 (N r)) false (t + 1)).count false)).count false =
      ((tape0 (N r)).take (head (tape0 (N r)) (tape1 (N r)) false (t + 1)).i).count false ∧
      (pre (tape0 (N r)) (tape1 (N r)) false (t + 1)).count false ≤
        (head (tape0 (N r)) (tape1 (N r)) false (t + 1)).i := by
    have h0 := hstep false
    cases ho : out (tape0 (N r)) (tape1 (N r)) false t
    · rw [ho] at h0; simp only [↓reduceIte] at h0
      rw [show (pre (tape0 (N r)) (tape1 (N r)) false (t + 1)).count false =
        (head (tape0 (N r)) (tape1 (N r)) false (t + 1)).i by omega]
      exact ⟨rfl, Nat.le_refl _⟩
    · rw [ho] at h0; simp only [Bool.true_eq_false, ↓reduceIte, Nat.add_zero] at h0
      have hs : (head (tape0 (N r)) (tape1 (N r)) false (t + 1)).s = true := by
        rw [head_s_succ]; exact ho
      have hi1 : 1 ≤ (head (tape0 (N r)) (tape1 (N r)) false (t + 1)).i := by omega
      have hpk := parked_X hf (t + 1) (by omega) hs hi1
      have hget : (tape0 (N r))[(head (tape0 (N r)) (tape1 (N r)) false (t + 1)).i - 1]? =
          some true := by
        rw [List.getElem?_eq_getElem (by omega)]; exact congrArg some hpk
      have e2 := count_take_succ_of (tape0 (N r)) hget false
      rw [show (head (tape0 (N r)) (tape1 (N r)) false (t + 1)).i - 1 + 1 =
        (head (tape0 (N r)) (tape1 (N r)) false (t + 1)).i by omega] at e2
      simp only [Bool.true_eq_false, ↓reduceIte, Nat.add_zero] at e2
      rw [show (pre (tape0 (N r)) (tape1 (N r)) false (t + 1)).count false =
        (head (tape0 (N r)) (tape1 (N r)) false (t + 1)).i - 1 by omega, e2]
      exact ⟨rfl, by omega⟩
  have eB : B (u (r + 1) + (t + 1) - 1) =
      ar (r + 1) + (pre (tape0 (N r)) (tape1 (N r)) false t).count false := by
    rw [show u (r + 1) + (t + 1) - 1 = u (r + 1) + t by omega, B_pos (r + 1) t (by omega),
      P_take_succ r t (by omega)]
  have hA0 := A_S0 r ((pre (tape0 (N r)) (tape1 (N r)) false (t + 1)).count false)
    (by have := key.2; omega)
  unfold RB
  rw [eB, B_pos (r + 1) (t + 1) ht, A_pos (r + 1) (t + 1) ht, P_take_succ r (t + 1) ht,
    show u (r + 1) + (t + 1) + 1 -
        (ar (r + 1) + (pre (tape0 (N r)) (tape1 (N r)) false (t + 1)).count true)
      = v r - 1 + (pre (tape0 (N r)) (tape1 (N r)) false (t + 1)).count false by omega,
    show u (r + 1) + (t + 1) + 1 -
        (ar (r + 1) + (pre (tape0 (N r)) (tape1 (N r)) false t).count false)
      = v r + (head (tape0 (N r)) (tape1 (N r)) false (t + 1)).j by omega,
    A_S1 r _ hle.2]
  omega

/-- **RB on the negative arch** of level `r`. -/
theorem RB_neg (r t : Nat) (ht : t + 1 ≤ (N r).length) : RB (v r + (t + 1)) := by
  have hf := (archFacts r).fits1
  have ha := ar_ge r; have hN := lenN r; have hve := v_eq r; have hu := u_ge r
  have hlP := lenP r
  have hL : ((P r).drop 2).length + (P r).dropLast.length = (N r).length := by
    simp [N, law1]
  have hi := head_i_eq (X := (P r).drop 2) (Y := (P r).dropLast) (ε := true) t
  have hj := head_j_eq (X := (P r).drop 2) (Y := (P r).dropLast) (ε := true) t
  simp only [↓reduceIte] at hi hj
  have hc := pre_count hf true (t + 1) (by omega)
  have hle := head_le_of_fits hf (t + 1) (by omega)
  have hZO := count_false_add_true (pre ((P r).drop 2) (P r).dropLast true t)
  rw [pre_length] at hZO
  unfold RB
  rw [B_neg r (t + 1) ht, A_neg r (t + 1) (by omega) ht, Nat.add_sub_cancel,
    show v r + (t + 1) - 1 = v r + t by omega, B_neg r t (by omega),
    N_take r (t + 1) ht, N_take r t (by omega),
    show v r + (t + 1) + 1 - (2 * ar r + 1 + (pre ((P r).drop 2) (P r).dropLast true t).count false)
      = u r + (head ((P r).drop 2) (P r).dropLast true (t + 1)).j by omega,
    show v r + (t + 1) + 1 - (2 * ar r + (pre ((P r).drop 2) (P r).dropLast true t).count true)
      = u r + 2 + (head ((P r).drop 2) (P r).dropLast true (t + 1)).i by omega,
    A_tapeY r _ hle.2, A_tapeX r _ hle.1]
  omega

/-- **RA on the negative arch** of level `r`. -/
theorem RA_neg (r t : Nat) (ht : t + 1 ≤ (N r).length) : RA (v r + (t + 1)) := by
  have ha := ar_ge r; have hN := lenN r; have hve := v_eq r; have hu := u_ge r
  have hlP := lenP r
  cases t with
  | zero =>
    unfold RA
    rw [show v r + (0 + 1) - 1 = v r by omega, A_v, B_v, A_neg r 1 (by omega) ht,
      show v r + (0 + 1) - 2 * ar r = u r + 1 by omega, B_u_one]
    simp
    omega
  | succ t =>
    have hf := (archFacts r).fits1
    have hL : ((P r).drop 2).length + (P r).dropLast.length = (N r).length := by
      simp [N, law1]
    have hi := head_i_eq (X := (P r).drop 2) (Y := (P r).dropLast) (ε := true) t
    have hj := head_j_eq (X := (P r).drop 2) (Y := (P r).dropLast) (ε := true) t
    simp only [↓reduceIte] at hi hj
    have hc := pre_count hf false (t + 1) (by omega)
    have hle := head_le_of_fits hf (t + 1) (by omega)
    have hZO := count_false_add_true (pre ((P r).drop 2) (P r).dropLast true t)
    rw [pre_length] at hZO
    have hZO1 := count_false_add_true (pre ((P r).drop 2) (P r).dropLast true (t + 1))
    rw [pre_length] at hZO1
    have h0 : out ((P r).drop 2) (P r).dropLast true 0 = false := by
      have := (archFacts r).N0
      rw [N, law1, interleave, List.getElem?_eq_getElem (by simp; omega), getElem_pre] at this
      exact Option.some.inj this
    have hstep := pre_succ (X := (P r).drop 2) (Y := (P r).dropLast) (ε := true) t
    have hZ := congrArg (List.count false) hstep
    rw [List.count_append, List.count_singleton] at hZ
    -- the `X`-head, seen from the zeros emitted so far
    have key : (((P r).drop 2).take
          ((pre ((P r).drop 2) (P r).dropLast true (t + 1)).count false - 1)).count false =
        (((P r).drop 2).take (head ((P r).drop 2) (P r).dropLast true (t + 1)).i).count false ∧
        (pre ((P r).drop 2) (P r).dropLast true (t + 1)).count false - 1 ≤
          (head ((P r).drop 2) (P r).dropLast true (t + 1)).i ∧
        1 ≤ (pre ((P r).drop 2) (P r).dropLast true (t + 1)).count false := by
      cases ho : out ((P r).drop 2) (P r).dropLast true t
      · rw [ho] at hZ; simp only [beq_self_eq_true, ↓reduceIte] at hZ
        rw [show (pre ((P r).drop 2) (P r).dropLast true (t + 1)).count false - 1 =
          (head ((P r).drop 2) (P r).dropLast true (t + 1)).i by omega]
        exact ⟨rfl, Nat.le_refl _, by omega⟩
      · rw [ho, if_neg (by decide), Nat.add_zero] at hZ
        have ht1 : 1 ≤ t := by
          rcases Nat.eq_zero_or_pos t with rfl | h
          · rw [h0] at ho; exact absurd ho (by decide)
          · exact h
        have hpos := count_pre_pos h0 ht1
        have hs : (head ((P r).drop 2) (P r).dropLast true (t + 1)).s = true := by
          rw [head_s_succ]; exact ho
        have hi1 : 1 ≤ (head ((P r).drop 2) (P r).dropLast true (t + 1)).i := by omega
        have hpk := parked_X hf (t + 1) (by omega) hs hi1
        have hget : ((P r).drop 2)[(head ((P r).drop 2) (P r).dropLast true (t + 1)).i - 1]? =
            some true := by
          rw [List.getElem?_eq_getElem (by omega)]; exact congrArg some hpk
        have e2 := count_take_succ_of ((P r).drop 2) hget false
        rw [show (head ((P r).drop 2) (P r).dropLast true (t + 1)).i - 1 + 1 =
          (head ((P r).drop 2) (P r).dropLast true (t + 1)).i by omega] at e2
        simp only [Bool.true_eq_false, ↓reduceIte, Nat.add_zero] at e2
        rw [show (pre ((P r).drop 2) (P r).dropLast true (t + 1)).count false - 1 =
          (head ((P r).drop 2) (P r).dropLast true (t + 1)).i - 1 by omega, e2]
        exact ⟨rfl, by omega, by omega⟩
    have hBX := B_tapeX r ((pre ((P r).drop 2) (P r).dropLast true (t + 1)).count false - 1)
      (by have := key.2.1; omega)
    unfold RA
    rw [A_neg r (t + 1 + 1) (by omega) ht, Nat.add_sub_cancel,
      show v r + (t + 1 + 1) - 1 = v r + (t + 1) by omega, B_neg r (t + 1) (by omega),
      A_neg r (t + 1) (by omega) (by omega), Nat.add_sub_cancel,
      N_take r (t + 1) (by omega), N_take r t (by omega),
      show v r + (t + 1 + 1) -
          (2 * ar r + (pre ((P r).drop 2) (P r).dropLast true (t + 1)).count true)
        = u r + 2 + ((pre ((P r).drop 2) (P r).dropLast true (t + 1)).count false - 1) by omega,
      show v r + (t + 1 + 1) -
          (2 * ar r + 1 + (pre ((P r).drop 2) (P r).dropLast true t).count false)
        = u r + (head ((P r).drop 2) (P r).dropLast true (t + 1)).j by omega,
      hBX, B_tapeY r _ hle.2]
    omega

end QTilde
