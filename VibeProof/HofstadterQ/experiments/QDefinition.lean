/-- Hofstadter's Q, padded to be total: a lookback that would leave `[1, n-1]` reads `q 0 = 0`.
Agrees with Hofstadter's Q wherever the latter is defined. -/
def q : Nat → Nat
  | 0 => 0
  | 1 => 1
  | 2 => 1
  | n + 3 => q (n + 3 - max 1 (q (n + 2))) + q (n + 3 - max 1 (q (n + 1)))
termination_by n => n
decreasing_by all_goals omega

/-- Relational spec (same shape as `Erdos422.IsHofstadterQ` in formal-conjectures, on ℕ). -/
def IsQ (f : Nat → Nat) : Prop :=
  f 1 = 1 ∧ f 2 = 1 ∧ ∀ n, 3 ≤ n → f (n - 1) < n ∧ f (n - 2) < n ∧ f n = f (n - f (n - 1)) + f (n - f (n - 2))

/-- Guy E31 / Hofstadter 1977: the Q-sequence never dies. Equivalent to `∀ n ≥ 1, q n ≤ n`. -/
def HofstadterQTotal : Prop := ∃ f, IsQ f

#eval (List.range 20).map q
