import Mathlib.Computability.MyhillNerode

/-! Scratch check (not part of any library): Problem 1 is equivalent to the unary language
`{1^n | c(n) = 1}` not being regular, via Mathlib's Myhill–Nerode theorem
`Language.isRegular_iff_finite_range_leftQuotient`. Definitions copied from
`Ruliology.CellularAutomata.Rule30Jen` / `Rule30Prize`. -/

namespace R30Test

def rule (a b c : Bool) : Bool := xor a (b || c)

def cell : Nat → Int → Bool
  | 0, p => decide (p = 0)
  | t + 1, p => rule (cell t (p - 1)) (cell t p) (cell t (p + 1))

def center (t : Nat) : Bool := cell t 0

def EventuallyPeriodic (f : Nat → Bool) : Prop :=
  ∃ T P : Nat, 0 < P ∧ ∀ t, T ≤ t → f (t + P) = f t

def Problem1 : Prop := ¬ EventuallyPeriodic center

/-- Periodicity iterates. -/
theorem periodic_mul {f : Nat → Bool} {T P : Nat} (h : ∀ t, T ≤ t → f (t + P) = f t) :
    ∀ k t, T ≤ t → f (t + k * P) = f t := by
  intro k
  induction k with
  | zero => intro t _; simp
  | succ k ih =>
    intro t ht
    rw [Nat.succ_mul, ← Nat.add_assoc, h (t + k * P) (by omega), ih t ht]

/-- A Boolean sequence is eventually periodic iff it has finitely many shifts. -/
theorem eventuallyPeriodic_iff_finite_shifts (f : Nat → Bool) :
    EventuallyPeriodic f ↔ (Set.range fun n => fun m => f (n + m)).Finite := by
  constructor
  · rintro ⟨T, P, hP, h⟩
    refine ((Finset.range (T + P)).finite_toSet.image fun n => fun m => f (n + m)).subset ?_
    rintro _ ⟨n, rfl⟩
    by_cases hn : n < T + P
    · exact ⟨n, by simpa using hn, rfl⟩
    · refine ⟨T + (n - T) % P, ?_, ?_⟩
      · have := Nat.mod_lt (n - T) hP
        simp only [Finset.coe_range, Set.mem_Iio]; omega
      · funext m
        have key := periodic_mul h ((n - T) / P) (T + (n - T) % P + m) (by omega)
        have e : T + (n - T) % P + m + (n - T) / P * P = n + m := by
          have := Nat.mod_add_div (n - T) P
          rw [Nat.mul_comm] at this
          omega
        rw [e] at key
        exact key.symm
  · intro hfin
    have : Finite (Set.range fun n => fun m => f (n + m)) := hfin.to_subtype
    obtain ⟨i, j, hij, hEq⟩ := Finite.exists_ne_map_eq_of_infinite
      (fun n => (⟨fun m => f (n + m), n, rfl⟩ : Set.range fun n => fun m => f (n + m)))
    have hEq' : (fun m => f (i + m)) = (fun m => f (j + m)) := congrArg Subtype.val hEq
    rcases Nat.lt_or_gt_of_ne hij with h | h
    · refine ⟨i, j - i, by omega, fun t ht => ?_⟩
      have := congrFun hEq' (t - i)
      rw [show i + (t - i) = t by omega, show j + (t - i) = t + (j - i) by omega] at this
      exact this.symm
    · refine ⟨j, i - j, by omega, fun t ht => ?_⟩
      have := congrFun hEq' (t - j)
      rw [show j + (t - j) = t by omega, show i + (t - j) = t + (i - j) by omega] at this
      exact this

/-- The unary language of the black times of a Boolean sequence. -/
def unaryLang (f : Nat → Bool) : Language Unit := {l : List Unit | f l.length = true}

theorem leftQuotient_unaryLang (f : Nat → Bool) (x : List Unit) :
    (unaryLang f).leftQuotient x = unaryLang (fun m => f (x.length + m)) := by
  ext y
  rw [Language.mem_leftQuotient]
  change f (x ++ y).length = true ↔ f (x.length + y.length) = true
  rw [List.length_append]

/-- Distinct sequences give distinct unary languages. -/
theorem unaryLang_injective : Function.Injective unaryLang := by
  intro f g h
  funext m
  have := congrArg (fun L : Language Unit => List.replicate m () ∈ L) h
  simp only [unaryLang] at this
  change (f (List.replicate m ()).length = true) = (g (List.replicate m ()).length = true) at this
  simp only [List.length_replicate] at this
  cases hf : f m <;> cases hg : g m <;> simp_all

theorem range_leftQuotient_unaryLang (f : Nat → Bool) :
    Set.range (unaryLang f).leftQuotient = unaryLang '' Set.range fun n => fun m => f (n + m) := by
  ext L
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨_, ⟨x.length, rfl⟩, (leftQuotient_unaryLang f x).symm⟩
  · rintro ⟨_, ⟨n, rfl⟩, rfl⟩
    exact ⟨List.replicate n (), by rw [leftQuotient_unaryLang, List.length_replicate]⟩

/-- A Boolean sequence is eventually periodic iff its unary language is regular. -/
theorem eventuallyPeriodic_iff_isRegular (f : Nat → Bool) :
    EventuallyPeriodic f ↔ (unaryLang f).IsRegular := by
  rw [Language.isRegular_iff_finite_range_leftQuotient, range_leftQuotient_unaryLang,
    Set.finite_image_iff unaryLang_injective.injOn, eventuallyPeriodic_iff_finite_shifts]

/-- **Problem 1 ⟺ the unary language `{1^n | c(n) = 1}` is not regular.** -/
theorem problem1_iff_not_regular : Problem1 ↔ ¬ (unaryLang center).IsRegular :=
  not_congr (eventuallyPeriodic_iff_isRegular center)

end R30Test

#print axioms R30Test.problem1_iff_not_regular
