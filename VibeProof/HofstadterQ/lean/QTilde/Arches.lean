import QTilde.Interleave

/-!
# Cloitre's arch words

Cloitre (arXiv:2604.06237, §2.3) builds two families of binary words by the interleaving laws

    N_r     = Interleave(P_r[2 : |P_r|), P_r[0 : |P_r| − 1), 1)          (Law 1)
    P_{r+1} = Interleave(00 N_r 1, 0 N_r, 0)                             (Law 2)

from `P₀ = 001011`, with level sizes `a₀ = 3`, `a_{r+1} = 4 a_r − 1`.

`archFacts` proves, for every level, the facts about these words that the well-definedness proof
uses: lengths, letter counts, first and last letters, and exact fit of both laws (Cloitre's
Lemmas 2.6–2.8 and 2.10). Cloitre's height (Dyck-path) invariants are not needed for
well-definedness and are not formalized here.
-/

namespace QTilde

/-- Cloitre's level sizes: `a₀ = 3`, `a_{r+1} = 4 a_r − 1`. -/
def ar : Nat → Nat
  | 0 => 3
  | r + 1 => 4 * ar r - 1

theorem ar_ge (r : Nat) : 3 ≤ ar r := by
  induction r with
  | zero => decide
  | succ r ih => simp only [ar]; omega

/-- Law 1: `N = Interleave(P[2 : |P|), P[0 : |P| − 1), 1)`. -/
def law1 (P : List Bool) : List Bool := interleave (P.drop 2) P.dropLast true

/-- The first tape of Law 2, `00 N 1`. -/
def tape0 (N : List Bool) : List Bool := [false, false] ++ N ++ [true]

/-- The second tape of Law 2, `0 N`. -/
def tape1 (N : List Bool) : List Bool := [false] ++ N

/-- The positive arch words `P_r`. -/
def P : Nat → List Bool
  | 0 => [false, false, true, false, true, true]
  | r + 1 => interleave (tape0 (law1 (P r))) (tape1 (law1 (P r))) false

/-- The negative arch words `N_r`. -/
def N (r : Nat) : List Bool := law1 (P r)

theorem P_succ (r : Nat) : P (r + 1) = interleave (tape0 (N r)) (tape1 (N r)) false := rfl

/-! ### General word lemmas -/

variable {X Y : List Bool} {ε : Bool}

/-- Started in state `false`, the first letter emitted is the first letter of `X`. -/
theorem out_zero_false (hf : Fits X Y false) (hL : 0 < X.length + Y.length) :
    out X Y false 0 = X[0]'((hf 0 hL).1 rfl) :=
  out_eq_X hf hL rfl

/-- Started in state `true`, the first letter emitted is the first letter of `Y`. -/
theorem out_zero_true (hf : Fits X Y true) (hL : 0 < X.length + Y.length) :
    out X Y true 0 = Y[0]'((hf 0 hL).2 rfl) :=
  out_eq_Y hf hL rfl

/-- **The last two letters.** If the second tape ends with a one, so does the interleaving, twice:
a final read from the first tape would leave the second tape's head parked after its last letter,
which is a one, while in state zero. -/
theorem out_last_two (hf : Fits X Y ε) (hY : Y ≠ []) (hYl : Y.getLast hY = true)
    (hL : 2 ≤ X.length + Y.length) :
    out X Y ε (X.length + Y.length - 1) = true ∧ out X Y ε (X.length + Y.length - 2) = true := by
  have hYlen : 0 < Y.length := List.length_pos_iff.2 hY
  obtain ⟨L, hLdef⟩ : ∃ L, L = X.length + Y.length := ⟨_, rfl⟩
  rw [← hLdef] at hL ⊢
  have he := head_end hf
  rw [← hLdef] at he
  have hsucc : head X Y ε L = step X Y (head X Y ε (L - 1)) := by
    rw [← head_succ]; congr 1; omega
  have hj := head_j_succ (X := X) (Y := Y) (ε := ε) (L - 1)
  rw [show L - 1 + 1 = L by omega] at hj
  have hs : (head X Y ε (L - 1)).s = true := by
    cases hs : (head X Y ε (L - 1)).s
    · exfalso
      simp only [hs, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at hj
      have hp := parked_Y hf (L - 1) (by omega) hs (by omega)
      have : Y[(head X Y ε (L - 1)).j - 1]'(by omega) = Y.getLast hY := by
        rw [List.getLast_eq_getElem]; congr 1; omega
      rw [this, hYl] at hp
      exact Bool.noConfusion hp
    · rfl
  simp only [hs, ↓reduceIte] at hj
  refine ⟨?_, ?_⟩
  · rw [out_eq_Y hf (by omega) hs]
    calc Y[(head X Y ε (L - 1)).j] = Y.getLast hY := by
          rw [List.getLast_eq_getElem]; congr 1; omega
      _ = true := hYl
  · rw [show L - 2 = L - 1 - 1 by omega, ← head_s_succ, show L - 1 - 1 + 1 = L - 1 by omega]
    exact hs

theorem true_mem_drop {l : List Bool} (hl : l ≠ []) (hlast : l.getLast hl = true) {i : Nat}
    (hi : i < l.length) : true ∈ l.drop i := by
  have hne : l.drop i ≠ [] := by
    intro h; have := congrArg List.length h; simp at this; omega
  have := List.getLast_mem hne
  rwa [List.getLast_drop hne, hlast] at this

theorem eq_ff_cons {l : List Bool} (h0 : l[0]? = some false) (h1 : l[1]? = some false) :
    l = false :: false :: l.drop 2 := by
  match l, h0, h1 with
  | [], h0, _ => simp at h0
  | [_], _, h1 => simp at h1
  | a :: b :: rest, h0, h1 => simp at h0 h1; simp [h0, h1]

/-! ### The arch facts -/

/-- Everything the well-definedness proof uses about level `r`. -/
structure ArchFacts (r : Nat) : Prop where
  lenP : (P r).length = 2 * ar r
  zerosP : (P r).count false = ar r
  onesP : (P r).count true = ar r
  P0 : (P r)[0]? = some false
  P1 : (P r)[1]? = some false
  Plast : (P r)[2 * ar r - 1]? = some true
  Plast2 : (P r)[2 * ar r - 2]? = some true
  fits1 : Fits ((P r).drop 2) (P r).dropLast true
  lenN : (N r).length = 4 * ar r - 3
  zerosN : (N r).count false = 2 * ar r - 2
  onesN : (N r).count true = 2 * ar r - 1
  N0 : (N r)[0]? = some false
  Nlast : (N r)[4 * ar r - 4]? = some true
  Nlast2 : (N r)[4 * ar r - 5]? = some true
  fits2 : Fits (tape0 (N r)) (tape1 (N r)) false

/-- Law 1 and its consequences, from the facts about `P_r`. -/
theorem law1_facts {Pw : List Bool} {a : Nat} (ha : 3 ≤ a) (hlen : Pw.length = 2 * a)
    (hz : Pw.count false = a) (ho : Pw.count true = a)
    (h0 : Pw[0]? = some false) (h1 : Pw[1]? = some false)
    (hl : Pw[2 * a - 1]? = some true) (hl2 : Pw[2 * a - 2]? = some true) :
    Fits (Pw.drop 2) Pw.dropLast true ∧
    (law1 Pw).length = 4 * a - 3 ∧ (law1 Pw).count false = 2 * a - 2 ∧
    (law1 Pw).count true = 2 * a - 1 ∧ (law1 Pw)[0]? = some false ∧
    (law1 Pw)[4 * a - 4]? = some true ∧ (law1 Pw)[4 * a - 5]? = some true := by
  have hne : Pw ≠ [] := by intro h; simp [h] at hlen; omega
  have hlast : Pw.getLast hne = true := by
    rw [List.getLast_eq_getElem]
    have := hl; rw [List.getElem?_eq_some_iff] at this
    obtain ⟨_, e⟩ := this
    rw [← e]; congr 1; omega
  -- counts of the two tapes
  have hsplit := eq_ff_cons h0 h1
  have hzX : (Pw.drop 2).count false = a - 2 := by
    have := congrArg (List.count false) hsplit; simp at this; omega
  have hoX : (Pw.drop 2).count true = a := by
    have := congrArg (List.count true) hsplit; simp at this; omega
  have hdl := List.dropLast_concat_getLast hne
  have hzY : Pw.dropLast.count false = a := by
    have := congrArg (List.count false) hdl; rw [hlast] at this; simp at this; omega
  have hoY : Pw.dropLast.count true = a - 1 := by
    have := congrArg (List.count true) hdl; rw [hlast] at this; simp at this; omega
  have hlX : (Pw.drop 2).length = 2 * a - 2 := by simp [hlen]
  have hlY : Pw.dropLast.length = 2 * a - 1 := by simp [hlen]
  have hf : Fits (Pw.drop 2) Pw.dropLast true := by
    apply fits_of_inv
    · simp only [↓reduceIte]; omega
    · simp only [↓reduceIte]; omega
    · intro i hi
      rw [List.drop_drop]
      exact true_mem_drop hne hlast (by omega)
  have hYne : Pw.dropLast ≠ [] := by intro h; simp [h] at hlY; omega
  have hYlast : Pw.dropLast.getLast hYne = true := by
    rw [List.getLast_eq_getElem, List.getElem_dropLast]
    have := hl2; rw [List.getElem?_eq_some_iff] at this
    obtain ⟨_, e⟩ := this
    rw [← e]; congr 1; simp [hlen]; omega
  have hL : (Pw.drop 2).length + Pw.dropLast.length = 4 * a - 3 := by omega
  have h2 := out_last_two hf hYne hYlast (by omega)
  rw [hL] at h2
  refine ⟨hf, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [law1, interleave_length]; omega
  · rw [law1, count_interleave hf]; omega
  · rw [law1, count_interleave hf]; omega
  · rw [law1, interleave, List.getElem?_eq_getElem (by simp; omega), getElem_pre,
      out_zero_true hf (by omega)]
    simp only [List.getElem_dropLast]
    rw [List.getElem?_eq_some_iff] at h0
    obtain ⟨_, e⟩ := h0
    exact congrArg some e
  · rw [law1, interleave, List.getElem?_eq_getElem (by simp; omega), getElem_pre]
    rw [show 4 * a - 4 = 4 * a - 3 - 1 by omega]; exact congrArg some h2.1
  · rw [law1, interleave, List.getElem?_eq_getElem (by simp; omega), getElem_pre]
    rw [show 4 * a - 5 = 4 * a - 3 - 2 by omega]; exact congrArg some h2.2

/-- Law 2 and its consequences, from the facts about `N_r`. -/
theorem law2_facts {Nw : List Bool} {a : Nat} (ha : 3 ≤ a) (hlen : Nw.length = 4 * a - 3)
    (hz : Nw.count false = 2 * a - 2) (ho : Nw.count true = 2 * a - 1)
    (hl : Nw[4 * a - 4]? = some true) :
    Fits (tape0 Nw) (tape1 Nw) false ∧
    (interleave (tape0 Nw) (tape1 Nw) false).length = 2 * (4 * a - 1) ∧
    (interleave (tape0 Nw) (tape1 Nw) false).count false = 4 * a - 1 ∧
    (interleave (tape0 Nw) (tape1 Nw) false).count true = 4 * a - 1 ∧
    (interleave (tape0 Nw) (tape1 Nw) false)[0]? = some false ∧
    (interleave (tape0 Nw) (tape1 Nw) false)[1]? = some false ∧
    (interleave (tape0 Nw) (tape1 Nw) false)[2 * (4 * a - 1) - 1]? = some true ∧
    (interleave (tape0 Nw) (tape1 Nw) false)[2 * (4 * a - 1) - 2]? = some true := by
  have hl0 : (tape0 Nw).length = 4 * a := by simp [tape0, hlen]; omega
  have hl1 : (tape1 Nw).length = 4 * a - 2 := by simp [tape1, hlen]; omega
  have hf : Fits (tape0 Nw) (tape1 Nw) false := by
    apply fits_of_inv
    · simp [tape0, tape1, hz]; omega
    · simp [tape0, tape1, ho]; omega
    · intro i hi
      have hne : tape0 Nw ≠ [] := by simp [tape0]
      have hlast0 : (tape0 Nw).getLast hne = true := List.getLast_concat
      exact true_mem_drop hne hlast0 hi
  have hY : tape1 Nw ≠ [] := by simp [tape1]
  have hNne : Nw ≠ [] := by intro h; simp [h] at hlen; omega
  have hYl : (tape1 Nw).getLast hY = true := by
    simp only [tape1, List.singleton_append]
    rw [List.getLast_cons hNne, List.getLast_eq_getElem]
    rw [List.getElem?_eq_some_iff] at hl
    obtain ⟨hb, e⟩ := hl
    rw [← e]; congr 1; omega
  have hL : (tape0 Nw).length + (tape1 Nw).length = 2 * (4 * a - 1) := by omega
  have h2 := out_last_two hf hY hYl (by omega)
  rw [hL] at h2
  refine ⟨hf, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [interleave_length]; omega
  · rw [count_interleave hf]; simp [tape0, tape1, hz]; omega
  · rw [count_interleave hf]; simp [tape0, tape1, ho]; omega
  · rw [interleave, List.getElem?_eq_getElem (by simp; omega), getElem_pre,
      out_zero_false hf (by omega)]
    simp [tape0]
  · rw [interleave, List.getElem?_eq_getElem (by simp; omega), getElem_pre,
      out_eq_X hf (by omega) (by rw [head_succ]; simp [step, tape0])]
    simp [head_succ, step, tape0]
  · rw [interleave, List.getElem?_eq_getElem (by simp; omega), getElem_pre]
    exact congrArg some h2.1
  · rw [interleave, List.getElem?_eq_getElem (by simp; omega), getElem_pre]
    exact congrArg some h2.2

/-- **The arch facts hold at every level** (Cloitre's Lemmas 2.6–2.8 and 2.10, without the height
invariants). -/
theorem archFacts : ∀ r, ArchFacts r
  | 0 => by
    have hP : ∀ r, r = 0 → ArchFacts r := by
      intro r hr; subst hr
      have h1 := law1_facts (Pw := P 0) (a := 3) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
      have h2 := law2_facts (Nw := N 0) (a := 3) (by decide) h1.2.1 h1.2.2.1 h1.2.2.2.1
        h1.2.2.2.2.2.1
      exact ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, h1.1,
        h1.2.1, h1.2.2.1, h1.2.2.2.1, h1.2.2.2.2.1, h1.2.2.2.2.2.1, h1.2.2.2.2.2.2, h2.1⟩
    exact hP 0 rfl
  | r + 1 => by
    have ih := archFacts r
    have ha := ar_ge r
    have h2 := law2_facts (Nw := N r) (a := ar r) ha ih.lenN ih.zerosN ih.onesN ih.Nlast
    rw [← P_succ] at h2
    have har : ar (r + 1) = 4 * ar r - 1 := rfl
    rw [← har] at h2
    obtain ⟨-, hlen, hz, ho, h0, h1, hl, hl2⟩ := h2
    have h1' := law1_facts (Pw := P (r + 1)) (a := ar (r + 1)) (ar_ge _) hlen hz ho h0 h1 hl hl2
    have h2' := law2_facts (Nw := N (r + 1)) (a := ar (r + 1)) (ar_ge _) h1'.2.1 h1'.2.2.1
      h1'.2.2.2.1 h1'.2.2.2.2.2.1
    exact ⟨hlen, hz, ho, h0, h1, hl, hl2, h1'.1, h1'.2.1, h1'.2.2.1, h1'.2.2.2.1,
      h1'.2.2.2.2.1, h1'.2.2.2.2.2.1, h1'.2.2.2.2.2.2, h2'.1⟩

end QTilde
