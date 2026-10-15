/-! Independent verification of claim A1 (realization bijection for the ZBL).
No imports beyond core `Init`.  Definitions copied verbatim from ZBLCore.lean; then an
Int-indexed specification ("rule 30 on p ≤ -1, positions p ≥ 0 white") is defined independently,
the indexing claim "index i = position -(i+1)" is proved, and the bijection is restated and
re-proved for the specification. -/

namespace A1Check

def rn (x : Nat → Bool) : Nat → Bool
  | 0 => false
  | j + 1 => x j

def zstep (x : Nat → Bool) (i : Nat) : Bool := xor (x (i + 1)) (x i || rn x i)

def zorb (x : Nat → Bool) : Nat → Nat → Bool
  | 0 => x
  | t + 1 => zstep (zorb x t)

def cols (a : Nat → Bool) : Nat → Nat → Bool
  | 0, _ => false
  | 1, t => a t
  | k + 2, t => xor (cols a (k + 1) (t + 1)) (cols a (k + 1) t || cols a k t)

def lam (a : Nat → Bool) (i : Nat) : Bool := cols a (i + 1) 0

theorem zorb_succ (x : Nat → Bool) (t : Nat) : zorb x (t + 1) = zstep (zorb x t) := rfl

/-! ### Proofs written independently (not copied) -/

theorem xor_cancel_right (u v : Bool) : xor (xor u v) v = u := by
  cases u <;> cases v <;> rfl

theorem xor_inj_right {u w v : Bool} (h : xor u v = xor w v) : u = w := by
  cases u <;> cases w <;> cases v <;> simp_all

/-- the right-neighbour term equals `cols a i t` along a history whose rows are `cols` -/
theorem realize' (a : Nat → Bool) : ∀ t i, zorb (lam a) t i = cols a (i + 1) t := by
  intro t
  induction t with
  | zero => intro i; rfl
  | succ t ih =>
    intro i
    have hrn : rn (zorb (lam a) t) i = cols a i t := by
      cases i with
      | zero => rfl
      | succ j => exact ih j
    show xor (zorb (lam a) t (i + 1)) (zorb (lam a) t i || rn (zorb (lam a) t) i) = cols a (i + 1) (t + 1)
    rw [ih (i + 1), ih i, hrn]
    show xor (xor (cols a (i + 1) (t + 1)) (cols a (i + 1) t || cols a i t))
      (cols a (i + 1) t || cols a i t) = cols a (i + 1) (t + 1)
    exact xor_cancel_right _ _

theorem unique' {x a : Nat → Bool} (h : ∀ t, zorb x t 0 = a t) :
    ∀ k, (∀ t, zorb x t k = cols a (k + 1) t) ∧ (∀ t, zorb x t (k + 1) = cols a (k + 2) t) := by
  -- left permutivity of one ZBL step
  have lp : ∀ (y : Nat → Bool) (i : Nat), y (i + 1) = xor (zstep y i) (y i || rn y i) := by
    intro y i; unfold zstep; exact (xor_cancel_right _ _).symm
  intro k
  induction k with
  | zero =>
    refine ⟨h, fun t => ?_⟩
    rw [lp (zorb x t) 0, ← zorb_succ, h (t + 1), h t]
    rfl
  | succ k ih =>
    refine ⟨ih.2, fun t => ?_⟩
    rw [lp (zorb x t) (k + 1), ← zorb_succ, ih.2 (t + 1), ih.2 t]
    show xor (cols a (k + 2) (t + 1)) (cols a (k + 2) t || zorb x t k) = cols a (k + 3) t
    rw [ih.1 t]
    rfl

theorem realization' (a : Nat → Bool) :
    (∀ t, zorb (lam a) t 0 = a t) ∧ ∀ x, (∀ t, zorb x t 0 = a t) → x = lam a :=
  ⟨fun t => realize' a t 0, fun x h => funext fun i => (unique' h i).1 0⟩

/-! ### Independent Int-indexed specification -/

/-- one step of rule 30 on positions `p ≤ -1`; positions `p ≥ 0` are held white -/
def specStep (y : Int → Bool) (p : Int) : Bool :=
  if p ≤ -1 then xor (y (p - 1)) (y p || y (p + 1)) else false

def specOrb (y : Int → Bool) : Nat → Int → Bool
  | 0 => y
  | t + 1 => specStep (specOrb y t)

/-- index `i` ↦ position `-(i+1)`; nonnegative positions white -/
def embed (x : Nat → Bool) (p : Int) : Bool :=
  if p ≤ -1 then x (-p - 1).toNat else false

theorem embed_zstep (x : Nat → Bool) : embed (zstep x) = specStep (embed x) := by
  funext p
  show (if p ≤ -1 then zstep x (-p - 1).toNat else false) =
    (if p ≤ -1 then xor (embed x (p - 1)) (embed x p || embed x (p + 1)) else false)
  by_cases hp : p ≤ -1
  · rw [if_pos hp, if_pos hp]
    have e1 : embed x (p - 1) = x ((-p - 1).toNat + 1) := by
      unfold embed
      rw [if_pos (show p - 1 ≤ -1 by omega), show (-(p - 1) - 1).toNat = (-p - 1).toNat + 1 by omega]
    have e0 : embed x p = x (-p - 1).toNat := by unfold embed; rw [if_pos hp]
    have e2 : embed x (p + 1) = rn x (-p - 1).toNat := by
      by_cases hp1 : p + 1 ≤ -1
      · obtain ⟨j, hj⟩ : ∃ j : Nat, (-p - 1).toNat = j + 1 := ⟨(-p - 1).toNat - 1, by omega⟩
        unfold embed
        rw [if_pos hp1, hj, show (-(p + 1) - 1).toNat = j by omega]
        rfl
      · rw [show (-p - 1).toNat = 0 by omega]
        unfold embed
        rw [if_neg hp1]
        rfl
    rw [e1, e0, e2]
    rfl
  · rw [if_neg hp, if_neg hp]

theorem embed_zorb (x : Nat → Bool) : ∀ t, embed (zorb x t) = specOrb (embed x) t := by
  intro t
  induction t with
  | zero => rfl
  | succ t ih => rw [zorb_succ, embed_zstep, ih]; rfl

theorem embed_col (x : Nat → Bool) (t : Nat) : specOrb (embed x) t (-1) = zorb x t 0 := by
  rw [← embed_zorb]; rfl

theorem embed_inj {x y : Nat → Bool} (h : embed x = embed y) : x = y := by
  funext i
  have := congrFun h (-((i : Int) + 1))
  unfold embed at this
  rw [if_pos (by omega), if_pos (by omega), show (-(-((i : Int) + 1)) - 1).toNat = i by omega] at this
  exact this

/-- every configuration white on `p ≥ 0` is an embedded half-line row -/
theorem embed_surj {y : Int → Bool} (hy : ∀ p, 0 ≤ p → y p = false) : ∃ x, embed x = y := by
  refine ⟨fun i => y (-((i : Int) + 1)), funext fun p => ?_⟩
  show (if p ≤ -1 then y (-((((-p - 1).toNat : Nat) : Int) + 1)) else false) = y p
  by_cases hp : p ≤ -1
  · rw [if_pos hp, show -((((-p - 1).toNat : Nat) : Int) + 1) = p by omega]
  · rw [if_neg hp, hy p (by omega)]

/-- **Spec form of A1.**  For every target column `a` there is exactly one configuration that is
white on `p ≥ 0` and whose half-line rule-30 evolution (wall held white) has `a` at position `-1`. -/
theorem spec_realization (a : Nat → Bool) :
    ∃ y : Int → Bool, (∀ p, 0 ≤ p → y p = false) ∧ (∀ t, specOrb y t (-1) = a t) ∧
      ∀ z : Int → Bool, (∀ p, 0 ≤ p → z p = false) → (∀ t, specOrb z t (-1) = a t) → z = y := by
  refine ⟨embed (lam a), fun p hp => ?_, fun t => ?_, fun z hz hza => ?_⟩
  · unfold embed; rw [if_neg (by omega)]
  · rw [embed_col]; exact (realization' a).1 t
  · obtain ⟨x, rfl⟩ := embed_surj hz
    have : x = lam a := (realization' a).2 x fun t => by rw [← embed_col]; exact hza t
    rw [this]

/-- the specification step really is rule 30 `new = left xor (centre or right)` on `p ≤ -1`, with
the cell at `p = 0` read as white -/
example (y : Int → Bool) (hy0 : y 0 = false) :
    specStep y (-1) = xor (y (-2)) (y (-1) || false) := by
  unfold specStep; rw [if_pos (by omega), show (-1 : Int) + 1 = 0 by rfl, hy0]; rfl

end A1Check

-- the claimant's statement and mine agree verbatim on the core theorem shape
#check @A1Check.realization'
#check @A1Check.spec_realization
#print axioms A1Check.realize'
#print axioms A1Check.unique'
#print axioms A1Check.realization'
#print axioms A1Check.embed_zstep
#print axioms A1Check.spec_realization

-- numeric sanity: column -1 of lam a reproduces a (small t, exponential naive evaluation)
def a1 : Nat → Bool := fun t => t % 3 == 0 || t % 7 == 2
def a2 : Nat → Bool := fun t => t % 2 == 0 || t == 5 || t == 9
#eval (List.range 12).map (fun t => (A1Check.zorb (A1Check.lam a1) t 0, a1 t))
#eval (List.range 12).all (fun t => A1Check.zorb (A1Check.lam a1) t 0 == a1 t)
#eval (List.range 12).all (fun t => A1Check.zorb (A1Check.lam a2) t 0 == a2 t)
