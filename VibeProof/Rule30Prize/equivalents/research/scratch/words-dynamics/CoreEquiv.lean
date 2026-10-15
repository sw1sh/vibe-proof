/-! Scratch check (words-dynamics agent), core Lean only: two elementary reformulations of
Problem 1. Definitions copied verbatim from `Rule30Jen` / `Rule30Prize`. -/

namespace Scratch2

def rule (a b c : Bool) : Bool := xor a (b || c)

def cell : Nat → Int → Bool
  | 0, p => decide (p = 0)
  | t + 1, p => rule (cell t (p - 1)) (cell t p) (cell t (p + 1))

def EventuallyPeriodic (f : Nat → Bool) : Prop := ∃ T P : Nat, 0 < P ∧ ∀ t, T ≤ t → f (t + P) = f t

def center (t : Nat) : Bool := cell t 0

def Problem1 : Prop := ¬ EventuallyPeriodic center

/-- The shift on one-sided sequences. -/
def shift (n : Nat) (f : Nat → Bool) : Nat → Bool := fun t => f (n + t)

theorem eventuallyPeriodic_iff_shift (f : Nat → Bool) :
    EventuallyPeriodic f ↔ ∃ m n, m < n ∧ shift m f = shift n f := by
  constructor
  · rintro ⟨T, P, hP, h⟩
    refine ⟨T, T + P, by omega, funext fun t => ?_⟩
    simp only [shift]
    rw [show T + P + t = (T + t) + P by omega, h (T + t) (by omega)]
  · rintro ⟨m, n, hmn, h⟩
    refine ⟨m, n - m, by omega, fun t ht => ?_⟩
    have := congrFun h (t - m)
    simp only [shift] at this
    rw [show m + (t - m) = t by omega, show n + (t - m) = t + (n - m) by omega] at this
    exact this.symm

/-- **Problem 1 iff the shift orbit of the center column is injective** (infinite orbit). -/
theorem problem1_iff_shift_injective :
    Problem1 ↔ ∀ m n, shift m center = shift n center → m = n := by
  unfold Problem1
  rw [eventuallyPeriodic_iff_shift]
  constructor
  · intro h m n hmn
    rcases Nat.lt_trichotomy m n with hlt | heq | hgt
    · exact absurd ⟨m, n, hlt, hmn⟩ h
    · exact heq
    · exact absurd ⟨n, m, hgt, hmn.symm⟩ h
  · rintro h ⟨m, n, hlt, he⟩
    have := h m n he
    omega

def EventuallyConst (g : Nat → Bool) : Prop := ∃ K b, ∀ k, K ≤ k → g k = b

theorem decim_of_periodic {f : Nat → Bool} {T P : Nat} (hP : 0 < P)
    (h : ∀ t, T ≤ t → f (t + P) = f t) (r : Nat) :
    ∀ d, f (r + (T + d) * P) = f (r + T * P) := by
  intro d
  induction d with
  | zero => rfl
  | succ d ih =>
    have hle : T + d ≤ (T + d) * P := Nat.le_mul_of_pos_right _ hP
    rw [show r + (T + (d + 1)) * P = (r + (T + d) * P) + P by
        simp only [Nat.add_mul, Nat.one_mul]; omega,
      h _ (by omega), ih]

theorem uniform_K {f : Nat → Bool} {P : Nat}
    (h : ∀ r, r < P → EventuallyConst (fun k => f (r + k * P))) :
    ∀ n, n ≤ P → ∃ K, ∀ r, r < n → ∀ k, K ≤ k → f (r + (k + 1) * P) = f (r + k * P) := by
  intro n
  induction n with
  | zero => exact fun _ => ⟨0, fun r hr => absurd hr (Nat.not_lt_zero r)⟩
  | succ n ih =>
    intro hn
    obtain ⟨K₁, hK₁⟩ := ih (by omega)
    obtain ⟨K₂, b, hK₂⟩ := h n (by omega)
    refine ⟨max K₁ K₂, fun r hr k hk => ?_⟩
    rcases Nat.lt_or_ge r n with hrn | hrn
    · exact hK₁ r hrn k (by omega)
    · have hr' : r = n := by omega
      subst hr'
      exact (hK₂ (k + 1) (by omega)).trans (hK₂ k (by omega)).symm

/-- **Decimation form**: a sequence is eventually periodic iff for some `P > 0` every residue
class mod `P` is eventually constant. -/
theorem eventuallyPeriodic_iff_decimations (f : Nat → Bool) :
    EventuallyPeriodic f ↔
      ∃ P, 0 < P ∧ ∀ r, r < P → EventuallyConst (fun k => f (r + k * P)) := by
  constructor
  · rintro ⟨T, P, hP, h⟩
    refine ⟨P, hP, fun r _ => ⟨T, f (r + T * P), fun k hk => ?_⟩⟩
    have := decim_of_periodic hP h r (k - T)
    rwa [show T + (k - T) = k by omega] at this
  · rintro ⟨P, hP, h⟩
    obtain ⟨K, hK⟩ := uniform_K h P (Nat.le_refl P)
    refine ⟨K * P, P, hP, fun t ht => ?_⟩
    have hdiv : t % P + t / P * P = t := by
      have := Nat.mod_add_div t P
      rw [Nat.mul_comm] at this
      exact this
    have hk : K ≤ t / P := (Nat.le_div_iff_mul_le hP).2 ht
    have := hK (t % P) (Nat.mod_lt t hP) (t / P) hk
    rw [Nat.add_mul, Nat.one_mul, ← Nat.add_assoc, hdiv] at this
    exact this

/-- **Problem 1, decimation form**: for every `P > 0` some residue class mod `P` of the center
column is not eventually constant. (`P = 1` is `Rule30Prize.center_not_eventually_constant`.) -/
theorem problem1_iff_decimations :
    Problem1 ↔ ∀ P, 0 < P → ∃ r, r < P ∧ ¬ EventuallyConst (fun k => center (r + k * P)) := by
  unfold Problem1
  rw [eventuallyPeriodic_iff_decimations]
  constructor
  · intro h P hP
    refine Classical.byContradiction fun hne => h ⟨P, hP, fun r hr => ?_⟩
    exact Classical.byContradiction fun hc => hne ⟨r, hr, hc⟩
  · rintro h ⟨P, hP, hall⟩
    obtain ⟨r, hr, hnc⟩ := h P hP
    exact hnc (hall r hr)


/-- The XOR derivative of a sequence. -/
def deriv (f : Nat → Bool) : Nat → Bool := fun t => xor (f t) (f (t + 1))

theorem deriv_ep {f : Nat → Bool} (h : EventuallyPeriodic f) : EventuallyPeriodic (deriv f) := by
  obtain ⟨T, P, hP, h⟩ := h
  refine ⟨T, P, hP, fun t ht => ?_⟩
  simp only [deriv]
  rw [show t + P + 1 = (t + 1) + P by omega, h t ht, h (t + 1) (by omega)]

theorem ep_of_deriv_ep {f : Nat → Bool} (h : EventuallyPeriodic (deriv f)) : EventuallyPeriodic f := by
  obtain ⟨T, P, hP, h⟩ := h
  have hS : ∀ d, xor (f (T + d + P)) (f (T + d)) = xor (f (T + P)) (f T) := by
    intro d
    induction d with
    | zero => rfl
    | succ d ih =>
      have h1 := h (T + d) (by omega)
      simp only [deriv] at h1
      rw [show T + (d + 1) + P = T + d + P + 1 by omega, show T + (d + 1) = T + d + 1 by omega,
        ← ih]
      revert h1
      cases f (T + d + P) <;> cases f (T + d + P + 1) <;> cases f (T + d) <;>
        cases f (T + d + 1) <;> decide
  cases hs : xor (f (T + P)) (f T)
  · refine ⟨T, P, hP, fun t ht => ?_⟩
    have h1 := hS (t - T)
    rw [hs, show T + (t - T) = t by omega] at h1
    revert h1
    cases f (t + P) <;> cases f t <;> decide
  · refine ⟨T, 2 * P, by omega, fun t ht => ?_⟩
    have h1 := hS (t - T)
    have h2 := hS (t + P - T)
    rw [hs, show T + (t - T) = t by omega] at h1
    rw [hs, show T + (t + P - T) = t + P by omega] at h2
    rw [show t + 2 * P = t + P + P by omega]
    revert h1 h2
    cases f (t + P + P) <;> cases f (t + P) <;> cases f t <;> decide

/-- **Problem 1 is invariant under the XOR derivative**: the center column is eventually
periodic iff `t ↦ c(t) xor c(t+1)` is. -/
theorem problem1_iff_deriv : Problem1 ↔ ¬ EventuallyPeriodic (deriv center) :=
  ⟨fun h hd => h (ep_of_deriv_ep hd), fun h hc => h (deriv_ep hc)⟩

end Scratch2

#print axioms Scratch2.problem1_iff_shift_injective
#print axioms Scratch2.problem1_iff_decimations
#print axioms Scratch2.problem1_iff_deriv
