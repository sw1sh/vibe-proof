import Ruliology.CellularAutomata.Rule30Jen

/-! Independent kernel re-check of the period-4 traps (verify-p4traps-rigor scratch file). -/

namespace P4TrapCheck
open Ruliology.CellularAutomata.Rule30Jen

/-- Masked Jen (same statement and proof as newideas/MaskedJen.lean). -/
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

/-- One rule-30 step on a finite window: `[x0, x1, ..., x(n+1)] ↦ [rule x0 x1 x2, ..., rule x(n-1) xn x(n+1)]`. -/
def step3 : List Bool → List Bool
  | [] => []
  | a :: tl => match tl with
    | b :: c :: _ => rule a b c :: step3 tl
    | _ => []

/-- `col t q n = [cell t q, cell t (q+1), ..., cell t (q+n-1)]`. -/
def col (t : Nat) (q : Int) : Nat → List Bool
  | 0 => []
  | n + 1 => cell t q :: col t (q + 1) n

theorem step3_col (t : Nat) : ∀ (n : Nat) (q : Int),
    step3 (col t q (n + 2)) = col (t + 1) (q + 1) n := by
  intro n
  induction n with
  | zero => intro q; rfl
  | succ n ih =>
    intro q
    have h2 : col t (q + 1) (n + 2) = cell t (q + 1) :: cell t (q + 1 + 1) :: col t (q + 1 + 1 + 1) n := rfl
    have h1 : col t q (n + 1 + 2) = cell t q :: col t (q + 1) (n + 2) := rfl
    rw [h1]
    show (match col t (q + 1) (n + 2) with
      | b :: c :: _ => rule (cell t q) b c :: step3 (col t (q + 1) (n + 2))
      | _ => []) = col (t + 1) (q + 1) (n + 1)
    rw [ih (q + 1)]
    rw [h2]
    show rule (cell t q) (cell t (q + 1)) (cell t (q + 1 + 1)) :: col (t + 1) (q + 1 + 1) n =
      cell (t + 1) (q + 1) :: col (t + 1) (q + 1 + 1) n
    have hc : cell (t + 1) (q + 1) = rule (cell t (q + 1 - 1)) (cell t (q + 1)) (cell t (q + 1 + 1)) := rfl
    rw [hc, Int.add_sub_cancel]

theorem col_snoc (t : Nat) : ∀ (n : Nat) (q : Int), col t q (n + 1) = col t q n ++ [cell t (q + n)] := by
  intro n
  induction n with
  | zero => intro q; simp [col]
  | succ n ih =>
    intro q
    show cell t q :: col t (q + 1) (n + 1) = (cell t q :: col t (q + 1) n) ++ [cell t (q + ((n + 1 : Nat) : Int))]
    rw [ih (q + 1)]
    have : q + 1 + (n : Int) = q + ((n + 1 : Nat) : Int) := by omega
    rw [this]; rfl

/-- The true strip (cells `1..b`) at time `t+1` is the window step of `c(t) :: strip ++ [cell t (b+1)]`. -/
theorem strip_step (t b : Nat) :
    col (t + 1) 1 b = step3 (cell t 0 :: (col t 1 b ++ [cell t (1 + (b : Int))])) := by
  have h := step3_col t b 0
  have e1 : col t 0 (b + 2) = cell t 0 :: col t (0 + 1) (b + 1) := rfl
  rw [e1, col_snoc] at h
  have e2 : (0 : Int) + 1 = 1 := rfl
  rw [e2] at h
  exact h.symm

theorem col_head (t b : Nat) (hb : 0 < b) (q : Int) : (col t q b).head? = some (cell t q) := by
  cases b with
  | zero => omega
  | succ b => rfl

def memS (S : List (Nat × List Bool)) (ph : Nat) (l : List Bool) : Bool :=
  S.any (fun e => e.1 == ph && e.2 == l)

theorem memS_iff (S : List (Nat × List Bool)) (ph : Nat) (l : List Bool) :
    memS S ph l = true ↔ (ph, l) ∈ S := by
  unfold memS
  rw [List.any_eq_true]
  constructor
  · rintro ⟨⟨a, m⟩, he, h⟩
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨h1, h2⟩ := h
    subst h1; subst h2; exact he
  · intro h
    exact ⟨(ph, l), h, by simp⟩

/-- The certificate: closure under the strip relation for both values of column `b+1`, with column 0
equal to `wc φ` at phase `φ`, phases mod 4; and at white phases column 1 equals `g φ`. -/
def checkTrap (wc g : Nat → Bool) (S : List (Nat × List Bool)) : Bool :=
  S.all (fun e =>
    memS S ((e.1 + 1) % 4) (step3 (wc e.1 :: (e.2 ++ [false]))) &&
    memS S ((e.1 + 1) % 4) (step3 (wc e.1 :: (e.2 ++ [true]))) &&
    (wc e.1 || e.2.head? == some (g e.1)))

theorem trap_sound (b : Nat) (hb : 0 < b) (wc g : Nat → Bool) (S : List (Nat × List Bool))
    (hcheck : checkTrap wc g S = true)
    (T k T' : Nat) (hc : ∀ t, T ≤ t → cell t 0 = wc ((t + k) % 4)) (hT : T ≤ T')
    (hin : ((T' + k) % 4, col T' 1 b) ∈ S) : False := by
  have hall := List.all_eq_true.mp hcheck
  -- invariant: the true strip stays in S at the matching phase
  have inv : ∀ n, ((T' + n + k) % 4, col (T' + n) 1 b) ∈ S := by
    intro n
    induction n with
    | zero => simpa using hin
    | succ n ih =>
      have hx := hall _ ih
      simp only [Bool.and_eq_true] at hx
      obtain ⟨⟨hf, ht⟩, _⟩ := hx
      have hct : cell (T' + n) 0 = wc ((T' + n + k) % 4) := hc _ (by omega)
      have hph : ((T' + n + k) % 4 + 1) % 4 = (T' + (n + 1) + k) % 4 := by omega
      have hs := strip_step (T' + n) b
      rw [hct] at hs
      rw [show T' + (n + 1) = T' + n + 1 by omega, hs, ← show ((T' + n + k) % 4 + 1) % 4 = (T' + n + 1 + k) % 4 by omega]
      cases hr : cell (T' + n) (1 + (b : Int)) with
      | false => exact (memS_iff _ _ _).mp hf
      | true => exact (memS_iff _ _ _).mp ht
  -- column 1 at white times is a function of the phase
  have out : ∀ t, T' ≤ t → cell t 0 = false → cell t 1 = g ((t + k) % 4) := by
    intro t ht hw
    have hm := inv (t - T')
    rw [show T' + (t - T') = t by omega] at hm
    have hx := hall _ hm
    simp only [Bool.and_eq_true] at hx
    obtain ⟨_, ho⟩ := hx
    have hwc : wc ((t + k) % 4) = false := by rw [← hc t (by omega)]; exact hw
    simp only [hwc, Bool.false_or, beq_iff_eq] at ho
    rw [col_head t b hb 1] at ho
    exact Option.some.inj ho
  apply masked_jen 0 (T := T') (Q := 4) (by decide)
  · intro t ht
    rw [hc (t + 4) (by omega), hc t (by omega), show (t + 4 + k) % 4 = (t + k) % 4 by omega]
  · intro t ht hw
    have hw4 : cell (t + 4) 0 = false := by
      rw [hc (t + 4) (by omega), show (t + 4 + k) % 4 = (t + k) % 4 by omega, ← hc t (by omega)]; exact hw
    show cell (t + 4) 1 = cell t 1
    rw [out t ht hw, out (t + 4) (by omega) hw4, show (t + 4 + k) % 4 = (t + k) % 4 by omega]

/-- Trap for w = 0001, strip width 16, 109 states (from newideas/trap_0001_16.txt). -/
def S0001 : List (Nat × List Bool) := [
  (0, [false, false, true, false, true, false, false, false, false, false, true, false, false, false, false, false]),
  (0, [false, false, true, false, false, false, true, false, true, false, true, false, false, false, false, false]),
  (0, [false, false, true, false, true, false, false, false, false, false, true, true, false, false, false, false]),
  (0, [false, false, true, false, false, false, true, false, true, false, true, true, false, false, false, false]),
  (0, [false, false, true, false, true, false, false, false, false, false, true, false, true, false, false, false]),
  (0, [false, false, true, false, true, false, false, false, false, false, true, false, false, true, false, false]),
  (0, [false, false, true, false, false, false, true, false, true, false, true, false, false, true, false, false]),
  (0, [false, false, true, false, true, false, false, false, false, false, true, false, true, true, false, false]),
  (0, [false, false, true, false, false, false, true, false, true, false, true, false, false, false, true, false]),
  (0, [false, false, true, false, true, false, false, false, false, false, true, false, true, false, true, false]),
  (0, [false, false, true, false, false, false, true, false, true, false, true, true, false, true, true, false]),
  (0, [false, false, true, false, true, false, false, false, false, false, true, false, true, true, true, false]),
  (0, [false, false, true, false, true, false, false, false, false, false, true, false, false, false, false, true]),
  (0, [false, false, true, false, false, false, true, false, true, false, true, false, false, false, false, true]),
  (0, [false, false, true, false, true, false, false, false, false, false, true, true, false, false, false, true]),
  (0, [false, false, true, false, false, false, true, false, true, false, true, true, false, false, false, true]),
  (0, [false, false, true, false, true, false, false, false, false, false, true, false, true, false, false, true]),
  (0, [false, false, true, false, true, false, false, false, false, false, true, false, false, true, false, true]),
  (0, [false, false, true, false, false, false, true, false, true, false, true, false, false, true, false, true]),
  (0, [false, false, true, false, true, false, false, false, false, false, true, false, true, true, false, true]),
  (0, [false, false, true, false, false, false, true, false, true, false, true, false, false, false, true, true]),
  (0, [false, false, true, false, true, false, false, false, false, false, true, true, false, false, true, true]),
  (0, [false, false, true, false, false, false, true, false, true, false, true, true, false, false, true, true]),
  (0, [false, false, true, false, true, false, false, false, false, false, true, false, true, false, true, true]),
  (0, [false, false, true, false, false, false, true, false, true, false, true, false, false, true, true, true]),
  (0, [false, false, true, false, true, false, false, false, false, false, true, false, true, true, true, true]),
  (1, [false, true, true, true, false, true, true, false, true, false, true, true, false, false, false, false]),
  (1, [false, true, true, false, true, true, false, false, false, true, true, true, false, false, false, false]),
  (1, [false, true, true, true, false, true, true, false, true, false, true, false, true, false, false, false]),
  (1, [false, true, true, false, true, true, false, false, false, true, true, false, true, false, false, false]),
  (1, [false, true, true, true, false, true, true, false, true, false, true, false, false, true, false, false]),
  (1, [false, true, true, false, true, true, false, false, false, true, true, false, true, true, false, false]),
  (1, [false, true, true, true, false, true, true, false, true, false, true, true, true, true, false, false]),
  (1, [false, true, true, false, true, true, false, false, false, true, true, false, true, false, true, false]),
  (1, [false, true, true, true, false, true, true, false, true, false, true, true, false, true, true, false]),
  (1, [false, true, true, true, false, true, true, false, true, false, true, false, true, true, true, false]),
  (1, [false, true, true, false, true, true, false, false, false, true, true, false, true, true, true, false]),
  (1, [false, true, true, true, false, true, true, false, true, false, true, true, true, true, true, false]),
  (1, [false, true, true, false, true, true, false, false, false, true, true, true, true, true, true, false]),
  (1, [false, true, true, true, false, true, true, false, true, false, true, true, false, false, false, true]),
  (1, [false, true, true, false, true, true, false, false, false, true, true, true, false, false, false, true]),
  (1, [false, true, true, true, false, true, true, false, true, false, true, false, true, false, false, true]),
  (1, [false, true, true, false, true, true, false, false, false, true, true, false, true, false, false, true]),
  (1, [false, true, true, true, false, true, true, false, true, false, true, false, false, true, false, true]),
  (1, [false, true, true, false, true, true, false, false, false, true, true, false, true, true, false, true]),
  (1, [false, true, true, true, false, true, true, false, true, false, true, true, true, true, false, true]),
  (1, [false, true, true, false, true, true, false, false, false, true, true, true, true, true, false, true]),
  (1, [false, true, true, true, false, true, true, false, true, false, true, true, false, false, true, true]),
  (1, [false, true, true, false, true, true, false, false, false, true, true, true, false, false, true, true]),
  (1, [false, true, true, true, false, true, true, false, true, false, true, false, true, false, true, true]),
  (1, [false, true, true, false, true, true, false, false, false, true, true, false, true, false, true, true]),
  (1, [false, true, true, true, false, true, true, false, true, false, true, true, false, true, true, true]),
  (1, [false, true, true, false, true, true, false, false, false, true, true, false, true, true, true, true]),
  (1, [false, true, true, true, false, true, true, false, true, false, true, true, true, true, true, true]),
  (1, [false, true, true, false, true, true, false, false, false, true, true, true, true, true, true, true]),
  (2, [true, true, false, false, true, false, true, false, true, true, false, false, false, false, false, false]),
  (2, [true, true, false, false, false, true, false, false, true, false, true, false, false, false, false, false]),
  (2, [true, true, false, false, true, false, true, false, true, true, false, false, true, false, false, false]),
  (2, [true, true, false, false, false, true, false, false, true, false, true, false, true, false, false, false]),
  (2, [true, true, false, false, false, true, false, false, true, false, true, false, false, true, false, false]),
  (2, [true, true, false, false, true, false, true, false, true, true, false, false, true, true, false, false]),
  (2, [true, true, false, false, false, true, false, false, true, false, true, false, true, true, false, false]),
  (2, [true, true, false, false, false, true, false, false, true, false, true, false, false, false, true, false]),
  (2, [true, true, false, false, true, false, true, false, true, true, false, false, true, false, true, false]),
  (2, [true, true, false, false, false, true, false, false, true, false, true, false, true, false, true, false]),
  (2, [true, true, false, false, true, false, true, false, true, true, false, false, true, true, true, false]),
  (2, [true, true, false, false, false, true, false, false, true, false, true, false, true, true, true, false]),
  (2, [true, true, false, false, false, true, false, false, true, false, true, true, true, true, true, false]),
  (2, [true, true, false, false, true, false, true, false, true, true, false, false, false, false, false, true]),
  (2, [true, true, false, false, false, true, false, false, true, false, true, false, false, false, false, true]),
  (2, [true, true, false, false, true, false, true, false, true, true, false, false, true, false, false, true]),
  (2, [true, true, false, false, false, true, false, false, true, false, true, false, true, false, false, true]),
  (2, [true, true, false, false, false, true, false, false, true, false, true, false, false, true, false, true]),
  (2, [true, true, false, false, true, false, true, false, true, true, false, false, true, true, false, true]),
  (2, [true, true, false, false, false, true, false, false, true, false, true, false, true, true, false, true]),
  (2, [true, true, false, false, false, true, false, false, true, false, true, true, true, true, false, true]),
  (2, [true, true, false, false, false, true, false, false, true, false, true, false, false, false, true, true]),
  (2, [true, true, false, false, true, false, true, false, true, true, false, false, true, false, true, true]),
  (2, [true, true, false, false, false, true, false, false, true, false, true, false, true, false, true, true]),
  (2, [true, true, false, false, true, false, true, false, true, true, false, false, true, true, true, true]),
  (2, [true, true, false, false, false, true, false, false, true, false, true, false, true, true, true, true]),
  (2, [true, true, false, false, false, true, false, false, true, false, true, true, true, true, true, true]),
  (3, [true, false, true, true, true, false, true, false, true, false, true, false, false, false, false, false]),
  (3, [true, false, true, false, true, true, true, true, true, false, true, false, false, false, false, false]),
  (3, [true, false, true, false, true, true, true, true, true, false, true, true, false, false, false, false]),
  (3, [true, false, true, false, true, true, true, true, true, false, true, false, true, false, false, false]),
  (3, [true, false, true, true, true, false, true, false, true, false, true, true, true, false, false, false]),
  (3, [true, false, true, false, true, true, true, true, true, false, true, false, true, true, false, false]),
  (3, [true, false, true, true, true, false, true, false, true, false, true, true, true, true, false, false]),
  (3, [true, false, true, false, true, true, true, true, true, false, true, false, true, false, true, false]),
  (3, [true, false, true, true, true, false, true, false, true, false, true, true, true, false, true, false]),
  (3, [true, false, true, false, true, true, true, true, true, false, true, true, false, true, true, false]),
  (3, [true, false, true, false, true, true, true, true, true, false, true, true, true, true, true, false]),
  (3, [true, false, true, true, true, false, true, false, true, false, true, false, false, false, false, true]),
  (3, [true, false, true, false, true, true, true, true, true, false, true, false, false, false, false, true]),
  (3, [true, false, true, false, true, true, true, true, true, false, true, true, false, false, false, true]),
  (3, [true, false, true, false, true, true, true, true, true, false, true, false, true, false, false, true]),
  (3, [true, false, true, true, true, false, true, false, true, false, true, true, true, false, false, true]),
  (3, [true, false, true, false, true, true, true, true, true, false, true, false, true, true, false, true]),
  (3, [true, false, true, true, true, false, true, false, true, false, true, true, true, true, false, true]),
  (3, [true, false, true, false, true, true, true, true, true, false, true, true, true, true, false, true]),
  (3, [true, false, true, true, true, false, true, false, true, false, true, false, false, false, true, true]),
  (3, [true, false, true, false, true, true, true, true, true, false, true, true, false, false, true, true]),
  (3, [true, false, true, false, true, true, true, true, true, false, true, false, true, false, true, true]),
  (3, [true, false, true, true, true, false, true, false, true, false, true, true, true, false, true, true]),
  (3, [true, false, true, false, true, true, true, true, true, false, true, true, false, true, true, true]),
  (3, [true, false, true, false, true, true, true, true, true, false, true, false, true, true, true, true]),
  (3, [true, false, true, true, true, false, true, false, true, false, true, true, true, true, true, true]),
  (3, [true, false, true, false, true, true, true, true, true, false, true, true, true, true, true, true])]
def w0001 (φ : Nat) : Bool := [false, false, false, true].getD φ false
def g0001 (φ : Nat) : Bool := [false, false, true, false].getD φ false
theorem len0001 : S0001.length = 109 := by decide +kernel
theorem check0001 : checkTrap w0001 g0001 S0001 = true := by decide +kernel

/-- If `c(t) = w0001[(t+k) mod 4]` for all `t ≥ T`, the true strip (cells 1..16) is never in `S0001`
at the matching phase at any time `T' ≥ T`. -/
theorem no_entry0001 (T k T' : Nat) (hc : ∀ t, T ≤ t → cell t 0 = w0001 ((t + k) % 4)) (hT : T ≤ T') :
    ((T' + k) % 4, col T' 1 16) ∉ S0001 :=
  fun hin => trap_sound 16 (by decide) w0001 g0001 S0001 check0001 T k T' hc hT hin

/-- Trap for w = 0011, strip width 16, 188 states (from newideas/trap_0011_16.txt). -/
def S0011 : List (Nat × List Bool) := [
  (0, [false, true, false, true, false, false, false, false, false, true, false, false, false, false, false, false]),
  (0, [false, true, false, false, false, true, false, true, false, true, false, false, false, false, false, false]),
  (0, [false, true, false, true, false, false, false, false, false, true, true, false, false, false, false, false]),
  (0, [false, true, false, false, false, true, false, true, false, true, true, false, false, false, false, false]),
  (0, [false, true, false, true, false, false, false, false, false, true, false, true, false, false, false, false]),
  (0, [false, true, false, true, false, false, false, false, false, true, false, false, true, false, false, false]),
  (0, [false, true, false, false, false, true, false, true, false, true, false, false, true, false, false, false]),
  (0, [false, true, false, true, false, false, false, false, false, true, false, true, true, false, false, false]),
  (0, [false, true, false, false, false, true, false, true, false, true, false, false, false, true, false, false]),
  (0, [false, true, false, true, false, false, false, false, false, true, false, true, false, true, false, false]),
  (0, [false, true, false, false, false, true, false, true, false, true, true, false, true, true, false, false]),
  (0, [false, true, false, true, false, false, false, false, false, true, false, true, true, true, false, false]),
  (0, [false, true, false, true, false, false, false, false, false, true, false, false, false, false, true, false]),
  (0, [false, true, false, false, false, true, false, true, false, true, false, false, false, false, true, false]),
  (0, [false, true, false, true, false, false, false, false, false, true, false, true, false, false, true, false]),
  (0, [false, true, false, true, false, false, false, false, false, true, false, false, true, false, true, false]),
  (0, [false, true, false, false, false, true, false, true, false, true, false, false, false, true, true, false]),
  (0, [false, true, false, true, false, false, false, false, false, true, true, false, false, true, true, false]),
  (0, [false, true, false, false, false, true, false, true, false, true, true, false, false, true, true, false]),
  (0, [false, true, false, true, false, false, false, false, false, true, false, true, false, true, true, false]),
  (0, [false, true, false, false, false, true, false, true, false, true, false, false, true, true, true, false]),
  (0, [false, true, false, true, false, false, false, false, false, true, false, true, true, true, true, false]),
  (0, [false, true, false, true, false, false, false, false, false, true, false, false, false, false, false, true]),
  (0, [false, true, false, false, false, true, false, true, false, true, false, false, false, false, false, true]),
  (0, [false, true, false, true, false, false, false, false, false, true, true, false, false, false, false, true]),
  (0, [false, true, false, false, false, true, false, true, false, true, true, false, false, false, false, true]),
  (0, [false, true, false, true, false, false, false, false, false, true, false, true, false, false, false, true]),
  (0, [false, true, false, true, false, false, false, false, false, true, false, false, true, false, false, true]),
  (0, [false, true, false, false, false, true, false, true, false, true, false, false, true, false, false, true]),
  (0, [false, true, false, true, false, false, false, false, false, true, false, true, true, false, false, true]),
  (0, [false, true, false, false, false, true, false, true, false, true, false, false, false, true, false, true]),
  (0, [false, true, false, true, false, false, false, false, false, true, false, true, false, true, false, true]),
  (0, [false, true, false, false, false, true, false, true, false, true, true, false, true, true, false, true]),
  (0, [false, true, false, true, false, false, false, false, false, true, false, true, true, true, false, true]),
  (0, [false, true, false, true, false, false, false, false, false, true, false, false, false, false, true, true]),
  (0, [false, true, false, false, false, true, false, true, false, true, true, false, false, false, true, true]),
  (0, [false, true, false, true, false, false, false, false, false, true, false, true, false, false, true, true]),
  (0, [false, true, false, true, false, false, false, false, false, true, false, false, true, false, true, true]),
  (0, [false, true, false, false, false, true, false, true, false, true, false, false, true, false, true, true]),
  (0, [false, true, false, true, false, false, false, false, false, true, false, true, true, false, true, true]),
  (0, [false, true, false, false, false, true, false, true, false, true, false, false, false, true, true, true]),
  (0, [false, true, false, true, false, false, false, false, false, true, true, false, false, true, true, true]),
  (0, [false, true, false, true, false, false, false, false, false, true, false, true, false, true, true, true]),
  (0, [false, true, false, false, false, true, false, true, false, true, false, false, true, true, true, true]),
  (0, [false, true, false, true, false, false, false, false, false, true, false, true, true, true, true, true]),
  (1, [true, true, true, false, true, true, false, true, false, true, true, false, false, false, false, false]),
  (1, [true, true, false, true, true, false, false, false, true, true, true, false, false, false, false, false]),
  (1, [true, true, true, false, true, true, false, true, false, true, false, true, false, false, false, false]),
  (1, [true, true, false, true, true, false, false, false, true, true, false, true, false, false, false, false]),
  (1, [true, true, false, true, true, false, false, false, true, true, false, true, true, false, false, false]),
  (1, [true, true, true, false, true, true, false, true, false, true, true, true, true, false, false, false]),
  (1, [true, true, false, true, true, false, false, false, true, true, false, true, false, true, false, false]),
  (1, [true, true, true, false, true, true, false, true, false, true, true, false, true, true, false, false]),
  (1, [true, true, true, false, true, true, false, true, false, true, false, true, true, true, false, false]),
  (1, [true, true, false, true, true, false, false, false, true, true, false, true, true, true, false, false]),
  (1, [true, true, true, false, true, true, false, true, false, true, true, true, true, true, false, false]),
  (1, [true, true, false, true, true, false, false, false, true, true, true, true, true, true, false, false]),
  (1, [true, true, false, true, true, false, false, false, true, true, false, true, false, false, true, false]),
  (1, [true, true, true, false, true, true, false, true, false, true, false, false, true, false, true, false]),
  (1, [true, true, true, false, true, true, false, true, false, true, true, true, true, false, true, false]),
  (1, [true, true, false, true, true, false, false, false, true, true, true, true, true, false, true, false]),
  (1, [true, true, true, false, true, true, false, true, false, true, true, false, false, true, true, false]),
  (1, [true, true, false, true, true, false, false, false, true, true, true, false, false, true, true, false]),
  (1, [true, true, true, false, true, true, false, true, false, true, false, true, false, true, true, false]),
  (1, [true, true, false, true, true, false, false, false, true, true, false, true, false, true, true, false]),
  (1, [true, true, true, false, true, true, false, true, false, true, true, false, true, true, true, false]),
  (1, [true, true, false, true, true, false, false, false, true, true, false, true, true, true, true, false]),
  (1, [true, true, true, false, true, true, false, true, false, true, true, false, false, false, false, true]),
  (1, [true, true, false, true, true, false, false, false, true, true, true, false, false, false, false, true]),
  (1, [true, true, true, false, true, true, false, true, false, true, false, true, false, false, false, true]),
  (1, [true, true, false, true, true, false, false, false, true, true, false, true, false, false, false, true]),
  (1, [true, true, true, false, true, true, false, true, false, true, false, false, true, false, false, true]),
  (1, [true, true, false, true, true, false, false, false, true, true, false, true, true, false, false, true]),
  (1, [true, true, true, false, true, true, false, true, false, true, true, true, true, false, false, true]),
  (1, [true, true, false, true, true, false, false, false, true, true, false, true, false, true, false, true]),
  (1, [true, true, true, false, true, true, false, true, false, true, true, false, true, true, false, true]),
  (1, [true, true, true, false, true, true, false, true, false, true, false, true, true, true, false, true]),
  (1, [true, true, false, true, true, false, false, false, true, true, false, true, true, true, false, true]),
  (1, [true, true, true, false, true, true, false, true, false, true, true, true, true, true, false, true]),
  (1, [true, true, false, true, true, false, false, false, true, true, true, true, true, true, false, true]),
  (1, [true, true, true, false, true, true, false, true, false, true, true, false, false, false, true, true]),
  (1, [true, true, false, true, true, false, false, false, true, true, true, false, false, false, true, true]),
  (1, [true, true, true, false, true, true, false, true, false, true, false, true, false, false, true, true]),
  (1, [true, true, false, true, true, false, false, false, true, true, false, true, false, false, true, true]),
  (1, [true, true, true, false, true, true, false, true, false, true, false, false, true, false, true, true]),
  (1, [true, true, false, true, true, false, false, false, true, true, false, true, true, false, true, true]),
  (1, [true, true, false, true, true, false, false, false, true, true, true, true, true, false, true, true]),
  (1, [true, true, true, false, true, true, false, true, false, true, true, false, false, true, true, true]),
  (1, [true, true, false, true, true, false, false, false, true, true, true, false, false, true, true, true]),
  (1, [true, true, false, true, true, false, false, false, true, true, false, true, false, true, true, true]),
  (1, [true, true, true, false, true, true, false, true, false, true, true, false, true, true, true, true]),
  (1, [true, true, false, true, true, false, false, false, true, true, false, true, true, true, true, true]),
  (1, [true, true, true, false, true, true, false, true, false, true, true, true, true, true, true, true]),
  (1, [true, true, false, true, true, false, false, false, true, true, true, true, true, true, true, true]),
  (2, [true, false, false, true, false, true, false, true, true, false, false, false, false, false, false, false]),
  (2, [true, false, false, false, true, false, false, true, false, true, false, false, false, false, false, false]),
  (2, [true, false, false, true, false, true, false, true, true, false, false, true, false, false, false, false]),
  (2, [true, false, false, false, true, false, false, true, false, true, false, true, false, false, false, false]),
  (2, [true, false, false, false, true, false, false, true, false, true, false, false, true, false, false, false]),
  (2, [true, false, false, true, false, true, false, true, true, false, false, true, true, false, false, false]),
  (2, [true, false, false, false, true, false, false, true, false, true, false, true, true, false, false, false]),
  (2, [true, false, false, false, true, false, false, true, false, true, false, false, false, true, false, false]),
  (2, [true, false, false, true, false, true, false, true, true, false, false, true, false, true, false, false]),
  (2, [true, false, false, false, true, false, false, true, false, true, false, true, false, true, false, false]),
  (2, [true, false, false, true, false, true, false, true, true, false, false, true, true, true, false, false]),
  (2, [true, false, false, false, true, false, false, true, false, true, false, true, true, true, false, false]),
  (2, [true, false, false, true, false, true, false, true, true, false, false, false, false, false, true, false]),
  (2, [true, false, false, false, true, false, false, true, false, true, false, false, false, false, true, false]),
  (2, [true, false, false, true, false, true, false, true, true, false, false, true, false, false, true, false]),
  (2, [true, false, false, false, true, false, false, true, false, true, false, true, false, false, true, false]),
  (2, [true, false, false, false, true, false, false, true, false, true, false, false, true, false, true, false]),
  (2, [true, false, false, false, true, false, false, true, false, true, true, true, true, false, true, false]),
  (2, [true, false, false, true, false, true, false, true, true, false, false, true, false, true, true, false]),
  (2, [true, false, false, false, true, false, false, true, false, true, false, true, false, true, true, false]),
  (2, [true, false, false, true, false, true, false, true, true, false, false, true, true, true, true, false]),
  (2, [true, false, false, false, true, false, false, true, false, true, false, true, true, true, true, false]),
  (2, [true, false, false, true, false, true, false, true, true, false, false, false, false, false, false, true]),
  (2, [true, false, false, false, true, false, false, true, false, true, false, false, false, false, false, true]),
  (2, [true, false, false, true, false, true, false, true, true, false, false, true, false, false, false, true]),
  (2, [true, false, false, false, true, false, false, true, false, true, false, true, false, false, false, true]),
  (2, [true, false, false, false, true, false, false, true, false, true, false, false, true, false, false, true]),
  (2, [true, false, false, true, false, true, false, true, true, false, false, true, true, false, false, true]),
  (2, [true, false, false, false, true, false, false, true, false, true, false, true, true, false, false, true]),
  (2, [true, false, false, false, true, false, false, true, false, true, false, false, false, true, false, true]),
  (2, [true, false, false, true, false, true, false, true, true, false, false, true, false, true, false, true]),
  (2, [true, false, false, false, true, false, false, true, false, true, false, true, false, true, false, true]),
  (2, [true, false, false, true, false, true, false, true, true, false, false, true, true, true, false, true]),
  (2, [true, false, false, false, true, false, false, true, false, true, false, true, true, true, false, true]),
  (2, [true, false, false, true, false, true, false, true, true, false, false, false, false, false, true, true]),
  (2, [true, false, false, false, true, false, false, true, false, true, false, false, false, false, true, true]),
  (2, [true, false, false, true, false, true, false, true, true, false, false, true, false, false, true, true]),
  (2, [true, false, false, false, true, false, false, true, false, true, false, true, false, false, true, true]),
  (2, [true, false, false, false, true, false, false, true, false, true, false, false, true, false, true, true]),
  (2, [true, false, false, true, false, true, false, true, true, false, false, true, true, false, true, true]),
  (2, [true, false, false, false, true, false, false, true, false, true, false, true, true, false, true, true]),
  (2, [true, false, false, false, true, false, false, true, false, true, true, true, true, false, true, true]),
  (2, [true, false, false, false, true, false, false, true, false, true, false, false, false, true, true, true]),
  (2, [true, false, false, true, false, true, false, true, true, false, false, true, false, true, true, true]),
  (2, [true, false, false, true, false, true, false, true, true, false, false, true, true, true, true, true]),
  (2, [true, false, false, false, true, false, false, true, false, true, true, true, true, true, true, true]),
  (3, [false, true, true, true, false, true, false, true, false, true, false, false, false, false, false, false]),
  (3, [false, true, false, true, true, true, true, true, false, true, false, false, false, false, false, false]),
  (3, [false, true, false, true, true, true, true, true, false, true, true, false, false, false, false, false]),
  (3, [false, true, false, true, true, true, true, true, false, true, false, true, false, false, false, false]),
  (3, [false, true, true, true, false, true, false, true, false, true, true, true, false, false, false, false]),
  (3, [false, true, false, true, true, true, true, true, false, true, false, true, true, false, false, false]),
  (3, [false, true, true, true, false, true, false, true, false, true, true, true, true, false, false, false]),
  (3, [false, true, false, true, true, true, true, true, false, true, false, true, false, true, false, false]),
  (3, [false, true, true, true, false, true, false, true, false, true, true, true, false, true, false, false]),
  (3, [false, true, false, true, true, true, true, true, false, true, true, false, true, true, false, false]),
  (3, [false, true, false, true, true, true, true, true, false, true, true, true, true, true, false, false]),
  (3, [false, true, false, true, true, true, true, true, false, true, false, false, false, false, true, false]),
  (3, [false, true, false, true, true, true, true, true, false, true, false, true, false, false, true, false]),
  (3, [false, true, true, true, false, true, false, true, false, true, true, true, false, false, true, false]),
  (3, [false, true, false, true, true, true, true, true, false, true, true, true, true, false, true, false]),
  (3, [false, true, true, true, false, true, false, true, false, true, false, false, false, true, true, false]),
  (3, [false, true, false, true, true, true, true, true, false, true, true, false, false, true, true, false]),
  (3, [false, true, false, true, true, true, true, true, false, true, false, true, false, true, true, false]),
  (3, [false, true, true, true, false, true, false, true, false, true, true, true, false, true, true, false]),
  (3, [false, true, false, true, true, true, true, true, false, true, true, false, true, true, true, false]),
  (3, [false, true, false, true, true, true, true, true, false, true, false, true, true, true, true, false]),
  (3, [false, true, true, true, false, true, false, true, false, true, true, true, true, true, true, false]),
  (3, [false, true, true, true, false, true, false, true, false, true, false, false, false, false, false, true]),
  (3, [false, true, false, true, true, true, true, true, false, true, true, false, false, false, false, true]),
  (3, [false, true, false, true, true, true, true, true, false, true, false, true, false, false, false, true]),
  (3, [false, true, true, true, false, true, false, true, false, true, true, true, false, false, false, true]),
  (3, [false, true, false, true, true, true, true, true, false, true, false, true, true, false, false, true]),
  (3, [false, true, true, true, false, true, false, true, false, true, true, true, true, false, false, true]),
  (3, [false, true, false, true, true, true, true, true, false, true, false, true, false, true, false, true]),
  (3, [false, true, true, true, false, true, false, true, false, true, true, true, false, true, false, true]),
  (3, [false, true, false, true, true, true, true, true, false, true, true, false, true, true, false, true]),
  (3, [false, true, false, true, true, true, true, true, false, true, true, true, true, true, false, true]),
  (3, [false, true, true, true, false, true, false, true, false, true, false, false, false, false, true, true]),
  (3, [false, true, false, true, true, true, true, true, false, true, false, false, false, false, true, true]),
  (3, [false, true, false, true, true, true, true, true, false, true, true, false, false, false, true, true]),
  (3, [false, true, false, true, true, true, true, true, false, true, false, true, false, false, true, true]),
  (3, [false, true, true, true, false, true, false, true, false, true, true, true, false, false, true, true]),
  (3, [false, true, false, true, true, true, true, true, false, true, false, true, true, false, true, true]),
  (3, [false, true, true, true, false, true, false, true, false, true, true, true, true, false, true, true]),
  (3, [false, true, false, true, true, true, true, true, false, true, true, true, true, false, true, true]),
  (3, [false, true, true, true, false, true, false, true, false, true, false, false, false, true, true, true]),
  (3, [false, true, false, true, true, true, true, true, false, true, true, false, false, true, true, true]),
  (3, [false, true, false, true, true, true, true, true, false, true, false, true, false, true, true, true]),
  (3, [false, true, true, true, false, true, false, true, false, true, true, true, false, true, true, true]),
  (3, [false, true, false, true, true, true, true, true, false, true, true, false, true, true, true, true]),
  (3, [false, true, false, true, true, true, true, true, false, true, false, true, true, true, true, true]),
  (3, [false, true, true, true, false, true, false, true, false, true, true, true, true, true, true, true]),
  (3, [false, true, false, true, true, true, true, true, false, true, true, true, true, true, true, true])]
def w0011 (φ : Nat) : Bool := [false, false, true, true].getD φ false
def g0011 (φ : Nat) : Bool := [false, true, false, false].getD φ false
theorem len0011 : S0011.length = 188 := by decide +kernel
theorem check0011 : checkTrap w0011 g0011 S0011 = true := by decide +kernel

/-- If `c(t) = w0011[(t+k) mod 4]` for all `t ≥ T`, the true strip (cells 1..16) is never in `S0011`
at the matching phase at any time `T' ≥ T`. -/
theorem no_entry0011 (T k T' : Nat) (hc : ∀ t, T ≤ t → cell t 0 = w0011 ((t + k) % 4)) (hT : T ≤ T') :
    ((T' + k) % 4, col T' 1 16) ∉ S0011 :=
  fun hin => trap_sound 16 (by decide) w0011 g0011 S0011 check0011 T k T' hc hT hin

/-- Trap for w = 0111, strip width 14, 188 states (from newideas/trap_0111_14.txt). -/
def S0111 : List (Nat × List Bool) := [
  (0, [false, true, false, true, false, true, true, false, false, false, false, false, false, false]),
  (0, [false, false, true, false, false, true, false, true, false, false, false, false, false, false]),
  (0, [false, true, false, true, false, true, true, false, false, true, false, false, false, false]),
  (0, [false, false, true, false, false, true, false, true, false, true, false, false, false, false]),
  (0, [false, false, true, false, false, true, false, true, false, false, true, false, false, false]),
  (0, [false, true, false, true, false, true, true, false, false, true, true, false, false, false]),
  (0, [false, false, true, false, false, true, false, true, false, true, true, false, false, false]),
  (0, [false, false, true, false, false, true, false, true, false, false, false, true, false, false]),
  (0, [false, true, false, true, false, true, true, false, false, true, false, true, false, false]),
  (0, [false, false, true, false, false, true, false, true, false, true, false, true, false, false]),
  (0, [false, true, false, true, false, true, true, false, false, true, true, true, false, false]),
  (0, [false, false, true, false, false, true, false, true, false, true, true, true, false, false]),
  (0, [false, true, false, true, false, true, true, false, false, false, false, false, true, false]),
  (0, [false, false, true, false, false, true, false, true, false, false, false, false, true, false]),
  (0, [false, true, false, true, false, true, true, false, false, true, false, false, true, false]),
  (0, [false, false, true, false, false, true, false, true, false, true, false, false, true, false]),
  (0, [false, false, true, false, false, true, false, true, false, false, true, false, true, false]),
  (0, [false, false, true, false, false, true, false, true, true, true, true, false, true, false]),
  (0, [false, true, false, true, false, true, true, false, false, true, false, true, true, false]),
  (0, [false, false, true, false, false, true, false, true, false, true, false, true, true, false]),
  (0, [false, true, false, true, false, true, true, false, false, true, true, true, true, false]),
  (0, [false, false, true, false, false, true, false, true, false, true, true, true, true, false]),
  (0, [false, true, false, true, false, true, true, false, false, false, false, false, false, true]),
  (0, [false, false, true, false, false, true, false, true, false, false, false, false, false, true]),
  (0, [false, true, false, true, false, true, true, false, false, true, false, false, false, true]),
  (0, [false, false, true, false, false, true, false, true, false, true, false, false, false, true]),
  (0, [false, false, true, false, false, true, false, true, false, false, true, false, false, true]),
  (0, [false, true, false, true, false, true, true, false, false, true, true, false, false, true]),
  (0, [false, false, true, false, false, true, false, true, false, true, true, false, false, true]),
  (0, [false, false, true, false, false, true, false, true, false, false, false, true, false, true]),
  (0, [false, true, false, true, false, true, true, false, false, true, false, true, false, true]),
  (0, [false, false, true, false, false, true, false, true, false, true, false, true, false, true]),
  (0, [false, true, false, true, false, true, true, false, false, true, true, true, false, true]),
  (0, [false, false, true, false, false, true, false, true, false, true, true, true, false, true]),
  (0, [false, true, false, true, false, true, true, false, false, false, false, false, true, true]),
  (0, [false, false, true, false, false, true, false, true, false, false, false, false, true, true]),
  (0, [false, true, false, true, false, true, true, false, false, true, false, false, true, true]),
  (0, [false, false, true, false, false, true, false, true, false, true, false, false, true, true]),
  (0, [false, false, true, false, false, true, false, true, false, false, true, false, true, true]),
  (0, [false, true, false, true, false, true, true, false, false, true, true, false, true, true]),
  (0, [false, false, true, false, false, true, false, true, false, true, true, false, true, true]),
  (0, [false, false, true, false, false, true, false, true, true, true, true, false, true, true]),
  (0, [false, false, true, false, false, true, false, true, false, false, false, true, true, true]),
  (0, [false, true, false, true, false, true, true, false, false, true, false, true, true, true]),
  (0, [false, true, false, true, false, true, true, false, false, true, true, true, true, true]),
  (0, [false, false, true, false, false, true, false, true, true, true, true, true, true, true]),
  (1, [true, true, false, true, false, true, false, true, false, false, false, false, false, false]),
  (1, [false, true, true, true, true, true, false, true, false, false, false, false, false, false]),
  (1, [false, true, true, true, true, true, false, true, true, false, false, false, false, false]),
  (1, [false, true, true, true, true, true, false, true, false, true, false, false, false, false]),
  (1, [true, true, false, true, false, true, false, true, true, true, false, false, false, false]),
  (1, [false, true, true, true, true, true, false, true, false, true, true, false, false, false]),
  (1, [true, true, false, true, false, true, false, true, true, true, true, false, false, false]),
  (1, [false, true, true, true, true, true, false, true, false, true, false, true, false, false]),
  (1, [true, true, false, true, false, true, false, true, true, true, false, true, false, false]),
  (1, [false, true, true, true, true, true, false, true, true, false, true, true, false, false]),
  (1, [false, true, true, true, true, true, false, true, true, true, true, true, false, false]),
  (1, [false, true, true, true, true, true, false, true, false, false, false, false, true, false]),
  (1, [false, true, true, true, true, true, false, true, false, true, false, false, true, false]),
  (1, [true, true, false, true, false, true, false, true, true, true, false, false, true, false]),
  (1, [false, true, true, true, true, true, false, true, true, true, true, false, true, false]),
  (1, [true, true, false, true, false, true, false, true, false, false, false, true, true, false]),
  (1, [false, true, true, true, true, true, false, true, true, false, false, true, true, false]),
  (1, [false, true, true, true, true, true, false, true, false, true, false, true, true, false]),
  (1, [true, true, false, true, false, true, false, true, true, true, false, true, true, false]),
  (1, [false, true, true, true, true, true, false, true, true, false, true, true, true, false]),
  (1, [false, true, true, true, true, true, false, true, false, true, true, true, true, false]),
  (1, [true, true, false, true, false, true, false, true, true, true, true, true, true, false]),
  (1, [true, true, false, true, false, true, false, true, false, false, false, false, false, true]),
  (1, [false, true, true, true, true, true, false, true, true, false, false, false, false, true]),
  (1, [false, true, true, true, true, true, false, true, false, true, false, false, false, true]),
  (1, [true, true, false, true, false, true, false, true, true, true, false, false, false, true]),
  (1, [false, true, true, true, true, true, false, true, false, true, true, false, false, true]),
  (1, [true, true, false, true, false, true, false, true, true, true, true, false, false, true]),
  (1, [false, true, true, true, true, true, false, true, false, true, false, true, false, true]),
  (1, [true, true, false, true, false, true, false, true, true, true, false, true, false, true]),
  (1, [false, true, true, true, true, true, false, true, true, false, true, true, false, true]),
  (1, [false, true, true, true, true, true, false, true, true, true, true, true, false, true]),
  (1, [true, true, false, true, false, true, false, true, false, false, false, false, true, true]),
  (1, [false, true, true, true, true, true, false, true, false, false, false, false, true, true]),
  (1, [false, true, true, true, true, true, false, true, true, false, false, false, true, true]),
  (1, [false, true, true, true, true, true, false, true, false, true, false, false, true, true]),
  (1, [true, true, false, true, false, true, false, true, true, true, false, false, true, true]),
  (1, [false, true, true, true, true, true, false, true, false, true, true, false, true, true]),
  (1, [true, true, false, true, false, true, false, true, true, true, true, false, true, true]),
  (1, [false, true, true, true, true, true, false, true, true, true, true, false, true, true]),
  (1, [true, true, false, true, false, true, false, true, false, false, false, true, true, true]),
  (1, [false, true, true, true, true, true, false, true, true, false, false, true, true, true]),
  (1, [false, true, true, true, true, true, false, true, false, true, false, true, true, true]),
  (1, [true, true, false, true, false, true, false, true, true, true, false, true, true, true]),
  (1, [false, true, true, true, true, true, false, true, true, false, true, true, true, true]),
  (1, [false, true, true, true, true, true, false, true, false, true, true, true, true, true]),
  (1, [true, true, false, true, false, true, false, true, true, true, true, true, true, true]),
  (1, [false, true, true, true, true, true, false, true, true, true, true, true, true, true]),
  (2, [false, true, false, false, false, false, false, true, false, false, false, false, false, false]),
  (2, [false, false, false, true, false, true, false, true, false, false, false, false, false, false]),
  (2, [false, true, false, false, false, false, false, true, true, false, false, false, false, false]),
  (2, [false, false, false, true, false, true, false, true, true, false, false, false, false, false]),
  (2, [false, true, false, false, false, false, false, true, false, true, false, false, false, false]),
  (2, [false, true, false, false, false, false, false, true, false, false, true, false, false, false]),
  (2, [false, false, false, true, false, true, false, true, false, false, true, false, false, false]),
  (2, [false, true, false, false, false, false, false, true, false, true, true, false, false, false]),
  (2, [false, false, false, true, false, true, false, true, false, false, false, true, false, false]),
  (2, [false, true, false, false, false, false, false, true, false, true, false, true, false, false]),
  (2, [false, false, false, true, false, true, false, true, true, false, true, true, false, false]),
  (2, [false, true, false, false, false, false, false, true, false, true, true, true, false, false]),
  (2, [false, true, false, false, false, false, false, true, false, false, false, false, true, false]),
  (2, [false, false, false, true, false, true, false, true, false, false, false, false, true, false]),
  (2, [false, true, false, false, false, false, false, true, false, true, false, false, true, false]),
  (2, [false, true, false, false, false, false, false, true, false, false, true, false, true, false]),
  (2, [false, false, false, true, false, true, false, true, false, false, false, true, true, false]),
  (2, [false, true, false, false, false, false, false, true, true, false, false, true, true, false]),
  (2, [false, false, false, true, false, true, false, true, true, false, false, true, true, false]),
  (2, [false, true, false, false, false, false, false, true, false, true, false, true, true, false]),
  (2, [false, false, false, true, false, true, false, true, false, false, true, true, true, false]),
  (2, [false, true, false, false, false, false, false, true, false, true, true, true, true, false]),
  (2, [false, true, false, false, false, false, false, true, false, false, false, false, false, true]),
  (2, [false, false, false, true, false, true, false, true, false, false, false, false, false, true]),
  (2, [false, true, false, false, false, false, false, true, true, false, false, false, false, true]),
  (2, [false, false, false, true, false, true, false, true, true, false, false, false, false, true]),
  (2, [false, true, false, false, false, false, false, true, false, true, false, false, false, true]),
  (2, [false, true, false, false, false, false, false, true, false, false, true, false, false, true]),
  (2, [false, false, false, true, false, true, false, true, false, false, true, false, false, true]),
  (2, [false, true, false, false, false, false, false, true, false, true, true, false, false, true]),
  (2, [false, false, false, true, false, true, false, true, false, false, false, true, false, true]),
  (2, [false, true, false, false, false, false, false, true, false, true, false, true, false, true]),
  (2, [false, false, false, true, false, true, false, true, true, false, true, true, false, true]),
  (2, [false, true, false, false, false, false, false, true, false, true, true, true, false, true]),
  (2, [false, true, false, false, false, false, false, true, false, false, false, false, true, true]),
  (2, [false, false, false, true, false, true, false, true, true, false, false, false, true, true]),
  (2, [false, true, false, false, false, false, false, true, false, true, false, false, true, true]),
  (2, [false, true, false, false, false, false, false, true, false, false, true, false, true, true]),
  (2, [false, false, false, true, false, true, false, true, false, false, true, false, true, true]),
  (2, [false, true, false, false, false, false, false, true, false, true, true, false, true, true]),
  (2, [false, false, false, true, false, true, false, true, false, false, false, true, true, true]),
  (2, [false, true, false, false, false, false, false, true, true, false, false, true, true, true]),
  (2, [false, true, false, false, false, false, false, true, false, true, false, true, true, true]),
  (2, [false, false, false, true, false, true, false, true, false, false, true, true, true, true]),
  (2, [false, true, false, false, false, false, false, true, false, true, true, true, true, true]),
  (3, [true, false, true, true, false, true, false, true, true, false, false, false, false, false]),
  (3, [false, true, true, false, false, false, true, true, true, false, false, false, false, false]),
  (3, [true, false, true, true, false, true, false, true, false, true, false, false, false, false]),
  (3, [false, true, true, false, false, false, true, true, false, true, false, false, false, false]),
  (3, [false, true, true, false, false, false, true, true, false, true, true, false, false, false]),
  (3, [true, false, true, true, false, true, false, true, true, true, true, false, false, false]),
  (3, [false, true, true, false, false, false, true, true, false, true, false, true, false, false]),
  (3, [true, false, true, true, false, true, false, true, true, false, true, true, false, false]),
  (3, [true, false, true, true, false, true, false, true, false, true, true, true, false, false]),
  (3, [false, true, true, false, false, false, true, true, false, true, true, true, false, false]),
  (3, [true, false, true, true, false, true, false, true, true, true, true, true, false, false]),
  (3, [false, true, true, false, false, false, true, true, true, true, true, true, false, false]),
  (3, [false, true, true, false, false, false, true, true, false, true, false, false, true, false]),
  (3, [true, false, true, true, false, true, false, true, false, false, true, false, true, false]),
  (3, [true, false, true, true, false, true, false, true, true, true, true, false, true, false]),
  (3, [false, true, true, false, false, false, true, true, true, true, true, false, true, false]),
  (3, [true, false, true, true, false, true, false, true, true, false, false, true, true, false]),
  (3, [false, true, true, false, false, false, true, true, true, false, false, true, true, false]),
  (3, [true, false, true, true, false, true, false, true, false, true, false, true, true, false]),
  (3, [false, true, true, false, false, false, true, true, false, true, false, true, true, false]),
  (3, [true, false, true, true, false, true, false, true, true, false, true, true, true, false]),
  (3, [false, true, true, false, false, false, true, true, false, true, true, true, true, false]),
  (3, [true, false, true, true, false, true, false, true, true, false, false, false, false, true]),
  (3, [false, true, true, false, false, false, true, true, true, false, false, false, false, true]),
  (3, [true, false, true, true, false, true, false, true, false, true, false, false, false, true]),
  (3, [false, true, true, false, false, false, true, true, false, true, false, false, false, true]),
  (3, [true, false, true, true, false, true, false, true, false, false, true, false, false, true]),
  (3, [false, true, true, false, false, false, true, true, false, true, true, false, false, true]),
  (3, [true, false, true, true, false, true, false, true, true, true, true, false, false, true]),
  (3, [false, true, true, false, false, false, true, true, false, true, false, true, false, true]),
  (3, [true, false, true, true, false, true, false, true, true, false, true, true, false, true]),
  (3, [true, false, true, true, false, true, false, true, false, true, true, true, false, true]),
  (3, [false, true, true, false, false, false, true, true, false, true, true, true, false, true]),
  (3, [true, false, true, true, false, true, false, true, true, true, true, true, false, true]),
  (3, [false, true, true, false, false, false, true, true, true, true, true, true, false, true]),
  (3, [true, false, true, true, false, true, false, true, true, false, false, false, true, true]),
  (3, [false, true, true, false, false, false, true, true, true, false, false, false, true, true]),
  (3, [true, false, true, true, false, true, false, true, false, true, false, false, true, true]),
  (3, [false, true, true, false, false, false, true, true, false, true, false, false, true, true]),
  (3, [true, false, true, true, false, true, false, true, false, false, true, false, true, true]),
  (3, [false, true, true, false, false, false, true, true, false, true, true, false, true, true]),
  (3, [false, true, true, false, false, false, true, true, true, true, true, false, true, true]),
  (3, [true, false, true, true, false, true, false, true, true, false, false, true, true, true]),
  (3, [false, true, true, false, false, false, true, true, true, false, false, true, true, true]),
  (3, [false, true, true, false, false, false, true, true, false, true, false, true, true, true]),
  (3, [true, false, true, true, false, true, false, true, true, false, true, true, true, true]),
  (3, [false, true, true, false, false, false, true, true, false, true, true, true, true, true]),
  (3, [true, false, true, true, false, true, false, true, true, true, true, true, true, true]),
  (3, [false, true, true, false, false, false, true, true, true, true, true, true, true, true])]
def w0111 (φ : Nat) : Bool := [false, true, true, true].getD φ false
def g0111 (φ : Nat) : Bool := [false, false, false, false].getD φ false
theorem len0111 : S0111.length = 188 := by decide +kernel
theorem check0111 : checkTrap w0111 g0111 S0111 = true := by decide +kernel

/-- If `c(t) = w0111[(t+k) mod 4]` for all `t ≥ T`, the true strip (cells 1..14) is never in `S0111`
at the matching phase at any time `T' ≥ T`. -/
theorem no_entry0111 (T k T' : Nat) (hc : ∀ t, T ≤ t → cell t 0 = w0111 ((t + k) % 4)) (hT : T ≤ T') :
    ((T' + k) % 4, col T' 1 14) ∉ S0111 :=
  fun hin => trap_sound 14 (by decide) w0111 g0111 S0111 check0111 T k T' hc hT hin

end P4TrapCheck

#print axioms P4TrapCheck.no_entry0001
#print axioms P4TrapCheck.no_entry0011
#print axioms P4TrapCheck.no_entry0111
