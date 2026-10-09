/-- `true` iff Hofstadter's Q is defined on `[1, N]` (no lookback leaves `[1, n-1]`). -/
def qDefinedUpTo (N : Nat) : Bool := Id.run do
  let mut a : Array Nat := #[0, 1, 1]
  for n in [3:N+1] do
    let x := a[n-1]!
    let y := a[n-2]!
    if n ≤ x || n ≤ y then return false
    a := a.push (a[n - x]! + a[n - y]!)
  return true

#eval qDefinedUpTo 100
theorem q_def_1e6 : qDefinedUpTo 1000000 = true := by native_decide
