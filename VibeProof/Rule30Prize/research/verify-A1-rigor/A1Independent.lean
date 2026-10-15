/-!
Independent re-check of claim A1 (truncated stripes), with NO imports.

`L s t p` is rule 30 (`left xor (center || right)`, left = `p - 1`, as in `Rule30Jen.cell`) on the
positions `p ≤ -1`, with every position `p ≥ 0` (in particular column 0) forced white, started from `s`.
-/
namespace VerifyA1

def rule (a b c : Bool) : Bool := xor a (b || c)

def L (s : Int → Bool) : Nat → Int → Bool
  | 0, p => if p < 0 then s p else false
  | t + 1, p => if p < 0 then rule (L s t (p - 1)) (L s t p) (L s t (p + 1)) else false

/-- Start: black exactly at positions `p = -k` with `k` odd and `1 ≤ k ≤ n`. -/
def start (n : Nat) (p : Int) : Bool := decide (p < 0) && decide (-p ≤ (n : Int)) && decide ((-p) % 2 = 1)

/-- Infinite stripe in Int coordinates. -/
def S (p : Int) : Bool := decide (p < 0) && decide ((-p) % 2 = 1)

theorem S_step (p : Int) (hp : p < 0) : rule (S (p - 1)) (S p) (S (p + 1)) = S p := by
  unfold rule S
  have hcases : (-p) % 2 = 0 ∨ (-p) % 2 = 1 := by omega
  rcases hcases with h | h
  · have h1 : (-(p - 1)) % 2 = 1 := by omega
    have h2 : p + 1 < 0 := by omega
    have h3 : (-(p + 1)) % 2 = 1 := by omega
    have h4 : p - 1 < 0 := by omega
    simp [h, h1, h2, h3, h4, hp]
  · have h1 : (-(p - 1)) % 2 = 0 := by omega
    have h4 : p - 1 < 0 := by omega
    simp [h, h1, h4, hp]

theorem L_wall (s : Int → Bool) (t : Nat) (p : Int) (hp : ¬ p < 0) : L s t p = false := by
  cases t <;> simp [L, hp]

theorem agree (n : Nat) (hn : n % 2 = 1) :
    ∀ (t : Nat) (p : Int), -p + (t : Int) ≤ (n : Int) + 1 → L (start n) t p = S p := by
  intro t
  induction t with
  | zero =>
    intro p hp
    by_cases h : p < 0
    · simp only [L, h, if_true]
      unfold start S
      by_cases h2 : -p ≤ (n : Int)
      · simp [h, h2]
      · have e : -p = (n : Int) + 1 := by omega
        have hodd : ((n : Int) + 1) % 2 = 0 := by omega
        simp [h, e, hodd]
    · rw [L_wall _ _ _ h]; simp [S, h]
  | succ t ih =>
    intro p hp
    by_cases h : p < 0
    · simp only [L, h, if_true]
      rw [ih (p - 1) (by omega), ih p (by omega), ih (p + 1) (by omega)]
      exact S_step p h
    · rw [L_wall _ _ _ h]; simp [S, h]

theorem antidiag (n : Nat) (hn : n % 2 = 1) :
    ∀ (t : Nat) (p : Int), p < 0 → -p + (t : Int) = (n : Int) + 2 → L (start n) t p = !S p := by
  intro t
  induction t with
  | zero =>
    intro p h hp
    simp only [L, h, if_true]
    have e : -p = (n : Int) + 2 := by omega
    have hodd : ((n : Int) + 2) % 2 = 1 := by omega
    have hgt : ¬ ((n : Int) + 2 ≤ (n : Int)) := by omega
    unfold start S
    simp [h, e, hodd, hgt]
  | succ t ih =>
    intro p h hp
    simp only [L, h, if_true]
    rw [ih (p - 1) (by omega) (by omega), agree n hn t p (by omega), agree n hn t (p + 1) (by omega)]
    have := S_step p h
    revert this
    unfold rule
    cases S (p - 1) <;> cases S p <;> cases S (p + 1) <;> simp

/-- Claim A1 in Int coordinates: column `-1` black at all `t ≤ n`, white at `t = n + 1`. -/
theorem main (n : Nat) (hn : n % 2 = 1) :
    (∀ t : Nat, t ≤ n → L (start n) t (-1) = true) ∧ L (start n) (n + 1) (-1) = false := by
  refine ⟨fun t ht => ?_, ?_⟩
  · rw [agree n hn t (-1) (by omega)]; decide
  · rw [antidiag n hn (n + 1) (-1) (by omega) (by push_cast; omega)]; decide

/-- `start n` is finitely supported: white at every position `p < -n` and at `p ≥ 0`. -/
theorem start_finite (n : Nat) (p : Int) (hp : p < -(n : Int) ∨ 0 ≤ p) : start n p = false := by
  unfold start
  rcases hp with hp | hp
  · have : ¬ (-p ≤ (n : Int)) := by omega
    simp [this]
  · have : ¬ p < 0 := by omega
    simp [this]

/-! ### The claim's depth-indexed ZBL (definition copied verbatim from ZBLBarrier.lean) agrees with `L`. -/

def z (s : Nat → Bool) : Nat → Nat → Bool
  | 0, k => if k = 0 then false else s k
  | t + 1, k => if k = 0 then false else xor (z s t (k + 1)) (z s t k || z s t (k - 1))

theorem z_eq_L (s : Int → Bool) :
    ∀ (t k : Nat), z (fun k => s (-(k : Int))) t k = L s t (-(k : Int)) := by
  intro t
  induction t with
  | zero =>
    intro k
    by_cases hk : k = 0
    · subst hk; simp [z, L]
    · have h : -(k : Int) < 0 := by omega
      simp only [z, L, hk, if_false]
      rw [if_pos h]
  | succ t ih =>
    intro k
    by_cases hk : k = 0
    · subst hk; simp [z, L]
    · have h : -(k : Int) < 0 := by omega
      simp only [z, L, hk, h, if_true, if_false, rule]
      rw [ih (k + 1), ih k, ih (k - 1)]
      have e1 : -((k + 1 : Nat) : Int) = -(k : Int) - 1 := by push_cast; omega
      have e2 : -((k - 1 : Nat) : Int) = -(k : Int) + 1 := by omega
      rw [e1, e2]

end VerifyA1

#print axioms VerifyA1.main
#print axioms VerifyA1.z_eq_L
#print axioms VerifyA1.start_finite
