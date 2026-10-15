import Ruliology.CellularAutomata.Rule30Prize

/-!
# Rule 30: rigid local structure forced by an alternating center column

Scratch development (smallperiods agent, 2026-10-15). Everything here is about a stretch of time
in which the center column alternates `0, 1, 0, 1, …` (the would-be period-2 behaviour). None of
it excludes period 2; it records the rigid relations such a stretch forces.

* `left_black_of_alt`: at a time with `c = 1` followed by `c = 0`, column `-1` is black.
* `col4_white_of_alt`: at a time `t` with `c = 0, 1, 0, 1, 0` on `[t, t+4]`, column `-4` is white.
* `no_AA`, `no_BB`, `no_ABAB`: with an alternating center, the column-1 pairs
  `(cell t 1, cell (t+1) 1)` (taken at the times `t` where `c t = 0`) never read `00 00`,
  `01 01` or `00 01 00 01`.
-/

namespace R30SmallPeriods2
open Ruliology.CellularAutomata.Rule30Jen
open Ruliology.CellularAutomata.Rule30Prize

def stepW (c : Bool) : List Bool → List Bool
  | [] => []
  | [_] => []
  | x :: y :: rest => rule c x y :: stepW x (y :: rest)

def win (t : Nat) (a : Int) : Nat → List Bool
  | 0 => []
  | n + 1 => cell t a :: win t (a + 1) n

theorem win_length (t : Nat) : ∀ (a : Int) (n : Nat), (win t a n).length = n
  | _, 0 => rfl
  | a, n + 1 => by simp [win, win_length t (a + 1) n]

theorem stepW_win (t : Nat) : ∀ (n : Nat) (a : Int),
    stepW (cell t (a - 1)) (win t a (n + 1)) = win (t + 1) a n
  | 0, a => by simp [win, stepW]
  | n + 1, a => by
    have ih := stepW_win t n (a + 1)
    rw [show a + 1 - 1 = a by omega] at ih
    show rule (cell t (a - 1)) (cell t a) (cell t (a + 1)) :: stepW (cell t a) (win t (a + 1) (n + 1))
      = cell (t + 1) a :: win (t + 1) (a + 1) n
    rw [ih]
    rfl

/-- Column-1 word of the right half: run the window with the given center values and record the
first window cell before each step. -/
def col1 : List Bool → List Bool → List Bool
  | [], _ => []
  | c :: cs, l => l.headD false :: col1 cs (stepW c l)

theorem col1_win : ∀ (cs : List Bool) (t n : Nat),
    (∀ i, (h : i < cs.length) → cell (t + i) 0 = cs[i]) →
    col1 cs (win t 1 (n + cs.length + 1)) = (List.range cs.length).map (fun i => cell (t + i) 1)
  | [], t, n, _ => rfl
  | c :: cs, t, n, h => by
    have h0 : cell t 0 = c := by simpa using h 0 (by simp)
    have hs : stepW c (win t 1 ((n + cs.length + 1) + 1)) = win (t + 1) 1 (n + cs.length + 1) := by
      have := stepW_win t (n + cs.length + 1) 1
      rw [show (1 : Int) - 1 = 0 by rfl, h0] at this
      exact this
    have ih := col1_win cs (t + 1) n (fun i hi => by
      have := h (i + 1) (by simp; omega)
      rw [show t + 1 + i = t + (i + 1) by omega]
      simpa using this)
    show (win t 1 (n + (cs.length + 1) + 1)).headD false :: col1 cs (stepW c (win t 1 (n + (cs.length + 1) + 1)))
      = (List.range (cs.length + 1)).map (fun i => cell (t + i) 1)
    rw [show n + (cs.length + 1) + 1 = (n + cs.length + 1) + 1 by omega, hs, ih, List.range_succ_eq_map]
    simp only [win, List.headD_cons, List.map_cons, List.map_map, Nat.add_zero]
    congr 1
    apply List.map_congr_left
    intro i _
    simp only [Function.comp, Nat.succ_eq_add_one]
    rw [show t + 1 + i = t + (i + 1) by omega]

/-- Alternating center values starting with `0`. -/
def alt (k : Nat) : List Bool := (List.range k).map (fun i => i % 2 == 1)

theorem alt_length (k : Nat) : (alt k).length = k := by simp [alt]

/-- Under an alternating center (white first), the column-1 word of length 8 never reads
`00 01 00 01`, and the words of length 4 never read `00 00` or `01 01`. -/
theorem alt_check_AA : (allLists 6).all (fun l => (col1 (alt 4) l) != [false, false, false, false]) = true := by
  decide +kernel
theorem alt_check_BB : (allLists 6).all (fun l => (col1 (alt 4) l) != [false, true, false, true]) = true := by
  decide +kernel
theorem alt_check_ABAB : (allLists 10).all
    (fun l => (col1 (alt 8) l) != [false, false, false, true, false, false, false, true]) = true := by
  decide +kernel

theorem alt_spec (t k : Nat) (h : ∀ i, i < k → center (t + i) = (i % 2 == 1)) :
    ∀ i, (hi : i < (alt k).length) → cell (t + i) 0 = (alt k)[i] := by
  intro i hi
  simp only [alt, List.getElem_map, List.getElem_range]
  exact h i (by simpa [alt_length] using hi)

theorem col1_alt (t k : Nat) (h : ∀ i, i < k → center (t + i) = (i % 2 == 1)) :
    col1 (alt k) (win t 1 (k + 2)) = (List.range k).map (fun i => cell (t + i) 1) := by
  have := col1_win (alt k) t 1 (alt_spec t k h)
  rw [alt_length] at this
  rw [show k + 2 = 1 + k + 1 by omega]
  exact this

theorem no_AA (t : Nat) (h : ∀ i, i < 4 → center (t + i) = (i % 2 == 1)) :
    ¬ (cell t 1 = false ∧ cell (t + 1) 1 = false ∧ cell (t + 2) 1 = false ∧ cell (t + 3) 1 = false) := by
  rintro ⟨h0, h1, h2, h3⟩
  have hw := col1_alt t 4 h
  have hmem : win t 1 (4 + 2) ∈ allLists 6 := by
    have := mem_allLists (win t 1 (4 + 2)); rwa [win_length] at this
  have hc := List.all_eq_true.1 alt_check_AA _ hmem
  rw [hw] at hc
  simp [List.range_succ, h0, h1, h2, h3] at hc

theorem no_BB (t : Nat) (h : ∀ i, i < 4 → center (t + i) = (i % 2 == 1)) :
    ¬ (cell t 1 = false ∧ cell (t + 1) 1 = true ∧ cell (t + 2) 1 = false ∧ cell (t + 3) 1 = true) := by
  rintro ⟨h0, h1, h2, h3⟩
  have hw := col1_alt t 4 h
  have hmem : win t 1 (4 + 2) ∈ allLists 6 := by
    have := mem_allLists (win t 1 (4 + 2)); rwa [win_length] at this
  have hc := List.all_eq_true.1 alt_check_BB _ hmem
  rw [hw] at hc
  simp [List.range_succ, h0, h1, h2, h3] at hc

theorem no_ABAB (t : Nat) (h : ∀ i, i < 8 → center (t + i) = (i % 2 == 1)) :
    ¬ (cell t 1 = false ∧ cell (t + 1) 1 = false ∧ cell (t + 2) 1 = false ∧ cell (t + 3) 1 = true ∧
       cell (t + 4) 1 = false ∧ cell (t + 5) 1 = false ∧ cell (t + 6) 1 = false ∧ cell (t + 7) 1 = true) := by
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  have hw := col1_alt t 8 h
  have hmem : win t 1 (8 + 2) ∈ allLists 10 := by
    have := mem_allLists (win t 1 (8 + 2)); rwa [win_length] at this
  have hc := List.all_eq_true.1 alt_check_ABAB _ hmem
  rw [hw] at hc
  simp [List.range_succ, h0, h1, h2, h3, h4, h5, h6, h7] at hc

/-! ### The left side -/

theorem a_eq (t : Nat) : cell t (-1) = xor (center (t + 1)) (center t || cell t 1) := by
  have := cell_left t 0
  rw [show (0 : Int) - 1 = -1 by rfl] at this
  exact this

theorem left_black_of_alt (t : Nat) (h0 : center t = true) (h1 : center (t + 1) = false) :
    cell t (-1) = true := by
  rw [a_eq, h0, h1]; rfl

/-- With `c = 0,1,0,1,0` on `[t, t+4]`, column `-4` is white at time `t`. -/
theorem col4_white_of_alt (t : Nat) (h0 : center t = false) (h1 : center (t + 1) = true)
    (h2 : center (t + 2) = false) (h3 : center (t + 3) = true) (h4 : center (t + 4) = false) :
    cell t (-4) = false := by
  have L : ∀ (s : Nat) (i : Int), cell s (i - 1) = xor (cell (s + 1) i) (cell s i || cell s (i + 1)) :=
    cell_left
  have k := L t (-3); have hA := L (t + 1) (-2); have hB := L t (-2)
  have f2 := L (t + 2) (-1); have f1 := L (t + 1) (-1); have f0 := L t (-1)
  have a3 := L (t + 3) 0; have a2 := L (t + 2) 0; have a1 := L (t + 1) 0; have a0 := L t 0
  simp only [show (-3 : Int) - 1 = -4 by rfl, show (-2 : Int) - 1 = -3 by rfl,
    show (-1 : Int) - 1 = -2 by rfl, show (0 : Int) - 1 = -1 by rfl,
    show (-3 : Int) + 1 = -2 by rfl, show (-2 : Int) + 1 = -1 by rfl,
    show (-1 : Int) + 1 = 0 by rfl, show (0 : Int) + 1 = 1 by rfl,
    show t + 1 + 1 = t + 2 by omega, show t + 2 + 1 = t + 3 by omega,
    show t + 3 + 1 = t + 4 by omega] at k hA hB f2 f1 f0 a3 a2 a1 a0
  unfold center at h0 h1 h2 h3 h4
  -- column 1 constraint: b(t) = 1 forces b(t+2) = 0
  have hb1 : cell (t + 1) 1 = (cell t 1 || cell t 2) := by
    show rule (cell t (1 - 1)) (cell t 1) (cell t (1 + 1)) = _
    rw [show (1 : Int) - 1 = 0 by rfl, h0, show (1 : Int) + 1 = 2 by rfl]
    cases cell t 1 <;> cases cell t 2 <;> rfl
  have hb2 : cell (t + 2) 1 = !(cell (t + 1) 1 || cell (t + 1) 2) := by
    show rule (cell (t + 1) (1 - 1)) (cell (t + 1) 1) (cell (t + 1) (1 + 1)) = _
    rw [show (1 : Int) - 1 = 0 by rfl, h1, show (1 : Int) + 1 = 2 by rfl]
    cases cell (t + 1) 1 <;> cases cell (t + 1) 2 <;> rfl
  rw [k, hA, hB, f2, f1, f0, a3, a2, a1, a0, h0, h1, h2, h3, h4, hb2, hb1]
  cases cell t 1 <;> cases cell t 2 <;> cases cell (t + 1) 2 <;> cases cell (t + 3) 1 <;> rfl

#print axioms no_ABAB
#print axioms col4_white_of_alt

#print axioms no_AA
#print axioms no_BB
#print axioms left_black_of_alt
#check @no_AA
#check @no_BB
#check @no_ABAB
#check @col4_white_of_alt
#check @left_black_of_alt
-- sanity: the length-8 word with alternating center from a concrete window
#eval col1 (alt 8) [true, false, true, true, false, false, true, false, true, true]
-- sanity: a false claim must fail (expect an error here)
example : (allLists 6).all (fun l => (col1 (alt 4) l) != [true, true, true, true]) = true := by
  decide +kernel
end R30SmallPeriods2
