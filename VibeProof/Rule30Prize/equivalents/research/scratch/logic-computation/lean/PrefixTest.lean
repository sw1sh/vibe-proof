import Mathlib.Computability.MyhillNerode

/-! Scratch check (not part of any library): Problem 1 is equivalent to the language of finite
prefixes of the center column not being regular (Myhill–Nerode). By Book (1977) "regular" may
be replaced by "context-free"; that step is not formalized here. -/

namespace R30Test

def rule (a b c : Bool) : Bool := xor a (b || c)

def cell : Nat → Int → Bool
  | 0, p => decide (p = 0)
  | t + 1, p => rule (cell t (p - 1)) (cell t p) (cell t (p + 1))

def center (t : Nat) : Bool := cell t 0

def EventuallyPeriodic (f : Nat → Bool) : Prop :=
  ∃ T P : Nat, 0 < P ∧ ∀ t, T ≤ t → f (t + P) = f t

def Problem1 : Prop := ¬ EventuallyPeriodic center

theorem periodic_mul {f : Nat → Bool} {T P : Nat} (h : ∀ t, T ≤ t → f (t + P) = f t) :
    ∀ k t, T ≤ t → f (t + k * P) = f t := by
  intro k
  induction k with
  | zero => intro t _; simp
  | succ k ih =>
    intro t ht
    rw [Nat.succ_mul, ← Nat.add_assoc, h (t + k * P) (by omega), ih t ht]

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

/-- The language of finite prefixes of `f`. -/
def prefLang (f : Nat → Bool) : Language Bool := {l : List Bool | l = (List.range l.length).map f}

theorem mem_prefLang {f : Nat → Bool} {l : List Bool} :
    l ∈ prefLang f ↔ l = (List.range l.length).map f := Iff.rfl

theorem range_mem_prefLang (f : Nat → Bool) (n : Nat) : (List.range n).map f ∈ prefLang f := by
  rw [mem_prefLang, List.length_map, List.length_range]

theorem map_range_add (f : Nat → Bool) (a b : Nat) :
    (List.range (a + b)).map f = (List.range a).map f ++ (List.range b).map (fun m => f (a + m)) := by
  rw [List.range_add, List.map_append, List.map_map]
  rfl

theorem append_mem_prefLang {f : Nat → Bool} {x y : List Bool} (hx : x ∈ prefLang f) :
    x ++ y ∈ prefLang f ↔ y ∈ prefLang (fun m => f (x.length + m)) := by
  rw [mem_prefLang, mem_prefLang, List.length_append, map_range_add]
  rw [mem_prefLang] at hx
  constructor
  · intro h
    conv_lhs at h => rw [hx]
    exact List.append_cancel_left h
  · intro h
    conv_lhs => rw [hx, h]

theorem append_not_mem_prefLang {f : Nat → Bool} {x : List Bool} (hx : x ∉ prefLang f)
    (y : List Bool) : x ++ y ∉ prefLang f := by
  intro h
  apply hx
  rw [mem_prefLang, List.length_append, map_range_add] at h
  have := congrArg (List.take x.length) h
  rw [List.take_left' rfl, List.take_left' (by simp)] at this
  exact this

theorem leftQuotient_prefLang_of_mem (f : Nat → Bool) {x : List Bool} (hx : x ∈ prefLang f) :
    (prefLang f).leftQuotient x = prefLang (fun m => f (x.length + m)) := by
  ext y
  rw [Language.mem_leftQuotient]
  exact append_mem_prefLang hx

theorem leftQuotient_prefLang_of_not_mem (f : Nat → Bool) {x : List Bool} (hx : x ∉ prefLang f) :
    (prefLang f).leftQuotient x = 0 := by
  ext y
  rw [Language.mem_leftQuotient]
  exact ⟨fun h => absurd h (append_not_mem_prefLang hx y), fun h => absurd h (Language.notMem_zero y)⟩

theorem prefLang_injective : Function.Injective prefLang := by
  intro f g h
  funext m
  have hm := range_mem_prefLang f (m + 1)
  rw [h, mem_prefLang, List.length_map, List.length_range, List.map_inj_left] at hm
  exact hm m (List.mem_range.2 (Nat.lt_succ_self m))

theorem range_leftQuotient_prefLang (f : Nat → Bool) :
    Set.range (prefLang f).leftQuotient ⊆
      insert 0 (prefLang '' Set.range fun n => fun m => f (n + m)) := by
  rintro _ ⟨x, rfl⟩
  by_cases hx : x ∈ prefLang f
  · rw [leftQuotient_prefLang_of_mem f hx]
    exact Or.inr ⟨_, ⟨x.length, rfl⟩, rfl⟩
  · rw [leftQuotient_prefLang_of_not_mem f hx]
    exact Or.inl rfl

theorem image_subset_range_leftQuotient (f : Nat → Bool) :
    prefLang '' (Set.range fun n => fun m => f (n + m)) ⊆ Set.range (prefLang f).leftQuotient := by
  rintro _ ⟨_, ⟨n, rfl⟩, rfl⟩
  refine ⟨(List.range n).map f, ?_⟩
  rw [leftQuotient_prefLang_of_mem f (range_mem_prefLang f n), List.length_map, List.length_range]

/-- A Boolean sequence is eventually periodic iff its prefix language is regular. -/
theorem eventuallyPeriodic_iff_prefLang_isRegular (f : Nat → Bool) :
    EventuallyPeriodic f ↔ (prefLang f).IsRegular := by
  rw [Language.isRegular_iff_finite_range_leftQuotient, eventuallyPeriodic_iff_finite_shifts]
  constructor
  · intro h
    exact ((h.image prefLang).insert 0).subset (range_leftQuotient_prefLang f)
  · intro h
    exact (Set.finite_image_iff prefLang_injective.injOn).1
      (h.subset (image_subset_range_leftQuotient f))

/-- **Problem 1 ⟺ the prefix language of the center column is not regular.** -/
theorem problem1_iff_prefixes_not_regular : Problem1 ↔ ¬ (prefLang center).IsRegular :=
  not_congr (eventuallyPeriodic_iff_prefLang_isRegular center)

end R30Test

#print axioms R30Test.problem1_iff_prefixes_not_regular
