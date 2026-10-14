import QTilde.Arches

/-!
# Cloitre's slow sequences

Cloitre (arXiv:2604.06237, §3.1) splits `Q̃` by parity, `Q̃(2m − 1) = 2a(m) − 1` and
`Q̃(2m) = 2b(m) − 1`, and builds `a`, `b` from the arch words: on the positive arch
`[u_r, v_r]` the increments of `a` are the letters of `P_r` (and those of `b` their complements), and
on the negative arch `[v_r, u_{r+1}]` the increments of `b` are the letters of `N_r`.

Here `A` and `B` are defined directly by the resulting closed forms: on each arch the value is the
starting value plus a letter count of a prefix of the arch word (`A_pos`, `B_pos`, `A_neg`,
`B_neg`). The arches tile all indices `m ≥ 4`: `v_r = u_r + |P_r|` and `u_{r+1} = v_r + |N_r|`.
-/

namespace QTilde

/-! ### Arch positions -/

/-- Start of the positive arch of level `r`: `u_r = 2 a_r − r − 2`. -/
def u (r : Nat) : Nat := 2 * ar r - r - 2

/-- Start of the negative arch of level `r`: `v_r = 4 a_r − r − 2`. -/
def v (r : Nat) : Nat := 4 * ar r - r - 2

theorem ar_succ (r : Nat) : ar (r + 1) = 4 * ar r - 1 := rfl

theorem ar_ge_r (r : Nat) : r + 3 ≤ ar r := by
  induction r with
  | zero => decide
  | succ r ih => rw [ar_succ]; omega

theorem v_eq (r : Nat) : v r = u r + 2 * ar r := by
  have := ar_ge_r r; simp only [u, v]; omega

theorem u_succ (r : Nat) : u (r + 1) = v r + (4 * ar r - 3) := by
  have := ar_ge_r r; simp only [u, v, ar_succ]; omega

theorem u_zero : u 0 = 4 := rfl

theorem u_ge (r : Nat) : r + 4 ≤ u r := by
  have := ar_ge_r r; simp only [u]; omega

theorem u_lt_v (r : Nat) : u r < v r := by
  have := ar_ge_r r; rw [v_eq]; omega

theorem v_lt_u_succ (r : Nat) : v r < u (r + 1) := by
  have := ar_ge_r r; rw [u_succ]; omega

theorem u_mono {r r' : Nat} (h : r ≤ r') : u r ≤ u r' := by
  induction r' with
  | zero => cases (Nat.le_zero.1 h); exact Nat.le_refl _
  | succ r' ih =>
    rcases Nat.lt_or_ge r (r' + 1) with h' | h'
    · have := ih (by omega); have := u_lt_v r'; have := v_lt_u_succ r'; omega
    · have : r = r' + 1 := by omega
      subst this; exact Nat.le_refl _

/-! ### The level of an index -/

/-- Search for the level `r` with `u_r < m ≤ u_{r+1}`, starting at level `r`. -/
def levelAux (m : Nat) : Nat → Nat → Nat
  | r, 0 => r
  | r, k + 1 => if m ≤ u (r + 1) then r else levelAux m (r + 1) k

/-- The level of an index `m > 4`: the `r` with `u_r < m ≤ u_{r+1}`. -/
def level (m : Nat) : Nat := levelAux m 0 m

theorem levelAux_eq {m r : Nat} (h1 : u r < m) (h2 : m ≤ u (r + 1)) :
    ∀ k r', r' ≤ r → r - r' < k → levelAux m r' k = r := by
  intro k
  induction k with
  | zero => intro r' _ h; omega
  | succ k ih =>
    intro r' hr' hk
    simp only [levelAux]
    rcases Nat.lt_or_ge r' r with hlt | hge
    · have : u (r' + 1) ≤ u r := u_mono hlt
      rw [if_neg (by omega)]
      exact ih (r' + 1) hlt (by omega)
    · have : r' = r := by omega
      subst this
      rw [if_pos h2]

theorem level_eq {m r : Nat} (h1 : u r < m) (h2 : m ≤ u (r + 1)) : level m = r :=
  levelAux_eq h1 h2 m 0 (Nat.zero_le _) (by have := u_ge r; omega)

/-! ### The slow sequences -/

/-- Cloitre's `a`: `Q̃(2m − 1) = 2 a(m) − 1`. -/
def A (m : Nat) : Nat :=
  if m ≤ 4 then [1, 1, 1, 2, 3].getD m 0
  else if m ≤ v (level m) then ar (level m) + ((P (level m)).take (m - u (level m))).count true
  else 2 * ar (level m) + 1 + ((N (level m)).take (m - v (level m) - 1)).count false

/-- Cloitre's `b`: `Q̃(2m) = 2 b(m) − 1`. -/
def B (m : Nat) : Nat :=
  if m ≤ 4 then [1, 1, 2, 2, 3].getD m 0
  else if m ≤ v (level m) then ar (level m) + ((P (level m)).take (m - u (level m))).count false
  else 2 * ar (level m) + ((N (level m)).take (m - v (level m))).count true

/-! ### Closed forms on the arches -/

theorem lenP (r : Nat) : (P r).length = 2 * ar r := (archFacts r).lenP
theorem lenN (r : Nat) : (N r).length = 4 * ar r - 3 := (archFacts r).lenN

theorem count_take_length (l : List Bool) (c : Bool) : (l.take l.length).count c = l.count c := by
  rw [List.take_length]

/-- Dropping a final one keeps the number of zeros. -/
theorem count_false_take_pred {l : List Bool} (h : l[l.length - 1]? = some true) :
    (l.take (l.length - 1)).count false = l.count false := by
  have hne : l ≠ [] := by intro e; simp [e] at h
  have hdl := List.dropLast_concat_getLast hne
  have hl : l.getLast hne = true := by
    rw [List.getLast_eq_getElem]
    rw [List.getElem?_eq_some_iff] at h
    obtain ⟨_, e⟩ := h; exact e
  rw [hl] at hdl
  have := congrArg (List.count false) hdl
  have hc : ([true] : List Bool).count false = 0 := rfl
  rw [List.count_append, hc, Nat.add_zero] at this
  rw [← List.dropLast_eq_take]
  exact this

/-- On the positive arch, between its two ends. -/
theorem A_pos_interior (r n : Nat) (h1 : 1 ≤ n) (hn : n ≤ 2 * ar r) :
    A (u r + n) = ar r + ((P r).take n).count true := by
  have hu := u_ge r
  have hlev : level (u r + n) = r :=
    level_eq (by omega) (by have := v_eq r; have := v_lt_u_succ r; omega)
  simp only [A, if_neg (show ¬ u r + n ≤ 4 by omega), hlev,
    if_pos (show u r + n ≤ v r by rw [v_eq]; omega), Nat.add_sub_cancel_left]

theorem B_pos_interior (r n : Nat) (h1 : 1 ≤ n) (hn : n ≤ 2 * ar r) :
    B (u r + n) = ar r + ((P r).take n).count false := by
  have hu := u_ge r
  have hlev : level (u r + n) = r :=
    level_eq (by omega) (by have := v_eq r; have := v_lt_u_succ r; omega)
  simp only [B, if_neg (show ¬ u r + n ≤ 4 by omega), hlev,
    if_pos (show u r + n ≤ v r by rw [v_eq]; omega), Nat.add_sub_cancel_left]

/-- On the negative arch, after its first index. -/
theorem A_neg (r s : Nat) (h1 : 1 ≤ s) (hs : s ≤ (N r).length) :
    A (v r + s) = 2 * ar r + 1 + ((N r).take (s - 1)).count false := by
  have hu := u_ge r; have huv := u_lt_v r
  have hlev : level (v r + s) = r :=
    level_eq (by omega) (by rw [u_succ, ← lenN]; omega)
  simp only [A, if_neg (show ¬ v r + s ≤ 4 by omega), hlev,
    if_neg (show ¬ v r + s ≤ v r by omega)]
  congr 3; omega

theorem B_neg_interior (r s : Nat) (h1 : 1 ≤ s) (hs : s ≤ (N r).length) :
    B (v r + s) = 2 * ar r + ((N r).take s).count true := by
  have hu := u_ge r; have huv := u_lt_v r
  have hlev : level (v r + s) = r :=
    level_eq (by omega) (by rw [u_succ, ← lenN]; omega)
  simp only [B, if_neg (show ¬ v r + s ≤ 4 by omega), hlev,
    if_neg (show ¬ v r + s ≤ v r by omega), Nat.add_sub_cancel_left]

/-- The arch starts: `a(u_r) = b(u_r) = a_r` (Cloitre's Lemma 3.1). -/
theorem A_u (r : Nat) : A (u r) = ar r := by
  cases r with
  | zero => rfl
  | succ r =>
    have hlen := lenN r
    have hN : (N r)[(N r).length - 1]? = some true := by
      rw [hlen, show 4 * ar r - 3 - 1 = 4 * ar r - 4 by have := ar_ge r; omega]
      exact (archFacts r).Nlast
    have h := A_neg r (N r).length (by have := ar_ge r; omega) (Nat.le_refl _)
    rw [show v r + (N r).length = u (r + 1) by rw [u_succ, lenN], count_false_take_pred hN,
      (archFacts r).zerosN] at h
    rw [h, ar_succ]; have := ar_ge r; omega

theorem B_u (r : Nat) : B (u r) = ar r := by
  cases r with
  | zero => rfl
  | succ r =>
    have hlen := lenN r
    have h := B_neg_interior r (N r).length (by have := ar_ge r; omega) (Nat.le_refl _)
    rw [show v r + (N r).length = u (r + 1) by rw [u_succ, lenN], List.take_length,
      (archFacts r).onesN] at h
    rw [h, ar_succ]; have := ar_ge r; omega

/-- **Positive arch** `[u_r, v_r]`: `a(u_r + n) = a_r + #ones(P_r[0, n))`. -/
theorem A_pos (r n : Nat) (hn : n ≤ 2 * ar r) : A (u r + n) = ar r + ((P r).take n).count true := by
  rcases Nat.eq_zero_or_pos n with rfl | h
  · simp [A_u]
  · exact A_pos_interior r n h hn

/-- **Positive arch**: `b(u_r + n) = a_r + #zeros(P_r[0, n))`. -/
theorem B_pos (r n : Nat) (hn : n ≤ 2 * ar r) : B (u r + n) = ar r + ((P r).take n).count false := by
  rcases Nat.eq_zero_or_pos n with rfl | h
  · simp [B_u]
  · exact B_pos_interior r n h hn

/-- The arch ends: `a(v_r) = b(v_r) = 2 a_r`. -/
theorem A_v (r : Nat) : A (v r) = 2 * ar r := by
  rw [v_eq, A_pos r _ (Nat.le_refl _),
    show (P r).take (2 * ar r) = P r by rw [← lenP]; exact List.take_length, (archFacts r).onesP]
  omega

theorem B_v (r : Nat) : B (v r) = 2 * ar r := by
  rw [v_eq, B_pos r _ (Nat.le_refl _),
    show (P r).take (2 * ar r) = P r by rw [← lenP]; exact List.take_length, (archFacts r).zerosP]
  omega

/-- **Negative arch** `[v_r, u_{r+1}]`: `b(v_r + s) = 2 a_r + #ones(N_r[0, s))`. -/
theorem B_neg (r s : Nat) (hs : s ≤ (N r).length) :
    B (v r + s) = 2 * ar r + ((N r).take s).count true := by
  rcases Nat.eq_zero_or_pos s with rfl | h
  · simp [B_v]
  · exact B_neg_interior r s h hs

end QTilde
