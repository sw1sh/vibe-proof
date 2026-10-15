
/-! Independent re-proof of Lemma A for an ARBITRARY rule-30 space-time pattern `x`
(any `x : Nat → Int → Bool` obeying the rule-30 recurrence), then specialised to the project's `cell`.
The finite core is stated as 11 nested Bool quantifiers (not `allLists`). -/

namespace VerifyLemmaA

def r30 (a b c : Bool) : Bool := a ^^ (b || c)

/-- one step of a finite row with given left neighbour; one cell shorter -/
def st (l : Bool) : List Bool → List Bool
  | a :: b :: rest => r30 l a b :: st a (b :: rest)
  | _ => []

/-- `k` steps with black left neighbour -/
def it : Nat → List Bool → List Bool
  | 0, L => L
  | k + 1, L => it k (st true L)

/-- cells `p .. p+n-1` of row `t` of the pattern `x` -/
def rw_ (x : Nat → Int → Bool) (t : Nat) (p : Int) : Nat → List Bool
  | 0 => []
  | n + 1 => x t p :: rw_ x t (p + 1) n

/-- the rule-30 recurrence, the only property of `x` used -/
def IsR30 (x : Nat → Int → Bool) : Prop :=
  ∀ (t : Nat) (p : Int), x (t + 1) p = r30 (x t (p - 1)) (x t p) (x t (p + 1))

theorem st_rw (x : Nat → Int → Bool) (hx : IsR30 x) (t : Nat) :
    ∀ (n : Nat) (p : Int), st (x t (p - 1)) (rw_ x t p (n + 1)) = rw_ x (t + 1) p n
  | 0, _ => rfl
  | n + 1, p => by
    have ih := st_rw x hx t n (p + 1)
    rw [show p + 1 - 1 = p by omega] at ih
    show r30 (x t (p - 1)) (x t p) (x t (p + 1)) :: st (x t p) (rw_ x t (p + 1) (n + 1)) =
      x (t + 1) p :: rw_ x (t + 1) (p + 1) n
    rw [ih, hx t p]

theorem it_rw (x : Nat → Int → Bool) (hx : IsR30 x) (m : Int) :
    ∀ (k n t : Nat), (∀ s, s < k → x (t + s) m = true) →
      it k (rw_ x t (m + 1) (n + k)) = rw_ x (t + k) (m + 1) n
  | 0, n, t, _ => by simp [it]
  | k + 1, n, t, h => by
    have h0 : x t m = true := by simpa using h 0 (by omega)
    have hstep : st true (rw_ x t (m + 1) (n + k + 1)) = rw_ x (t + 1) (m + 1) (n + k) := by
      have := st_rw x hx t (n + k) (m + 1)
      rw [show m + 1 - 1 = m by omega, h0] at this
      exact this
    have ih := it_rw x hx m k n (t + 1) (fun s hs => by
      have := h (s + 1) (by omega)
      rwa [show t + (s + 1) = t + 1 + s by omega] at this)
    show it k (st true (rw_ x t (m + 1) (n + (k + 1)))) = rw_ x (t + (k + 1)) (m + 1) n
    rw [show n + (k + 1) = n + k + 1 by omega, hstep, ih, show t + 1 + k = t + (k + 1) by omega]

/-- finite core, as 11 nested Boolean quantifiers (2048 cases), kernel-checked -/
theorem core : ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 : Bool,
    it 9 [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10] = [false, true] := by
  decide +kernel

/-- 8 steps are not enough: an explicit 10-cell row whose first cell comes out black -/
theorem eight_fails : ∃ b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 : Bool,
    (it 8 [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9]).head? = some true := by
  decide +kernel

/-- **Lemma A for any rule-30 space-time pattern.** -/
theorem lemmaA (x : Nat → Int → Bool) (hx : IsR30 x) (t : Nat) (m : Int)
    (h : ∀ s, s < 9 → x (t + s) m = true) :
    x (t + 9) (m + 1) = false ∧ x (t + 9) (m + 2) = true := by
  have h1 := it_rw x hx m 9 2 t h
  have e : rw_ x t (m + 1) (2 + 9) =
      [x t (m+1), x t (m+1+1), x t (m+1+1+1), x t (m+1+1+1+1), x t (m+1+1+1+1+1),
       x t (m+1+1+1+1+1+1), x t (m+1+1+1+1+1+1+1), x t (m+1+1+1+1+1+1+1+1),
       x t (m+1+1+1+1+1+1+1+1+1), x t (m+1+1+1+1+1+1+1+1+1+1),
       x t (m+1+1+1+1+1+1+1+1+1+1+1)] := rfl
  rw [e, core] at h1
  have e2 : rw_ x (t + 9) (m + 1) 2 = [x (t + 9) (m + 1), x (t + 9) (m + 1 + 1)] := rfl
  rw [e2] at h1
  simp only [List.cons.injEq] at h1
  exact ⟨h1.1.symm, by rw [show m + 2 = m + 1 + 1 by omega]; exact h1.2.1.symm⟩

end VerifyLemmaA


#print axioms VerifyLemmaA.lemmaA
#print axioms VerifyLemmaA.core
