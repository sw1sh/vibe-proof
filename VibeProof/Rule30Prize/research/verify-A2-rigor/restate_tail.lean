
/-! ## Independent restatements (verifier) -/
namespace IndepCheck
open Ruliology.CellularAutomata
open Ruliology.CellularAutomata.Rule30Jen

/-- zero-wall half-line rule 30 on Int positions `p < 0`; every `p ≥ 0` held white -/
def Z (s : Int → Bool) : Nat → Int → Bool
  | 0, p => if p < 0 then s p else false
  | t + 1, p => if p < 0 then rule (Z s t (p - 1)) (Z s t p) (Z s t (p + 1)) else false

theorem Z_nonneg (s : Int → Bool) (t : Nat) {p : Int} (hp : 0 ≤ p) : Z s t p = false := by
  cases t <;> simp [Z, show ¬ p < 0 by omega]

theorem Z_eq (s : Int → Bool) : ∀ t (i : Nat),
    Z s t (-((i + 1 : Nat) : Int)) = R30ProgA.zorb (fun i => s (-((i + 1 : Nat) : Int))) t i := by
  intro t
  induction t with
  | zero =>
    intro i
    show (if -((i + 1 : Nat) : Int) < 0 then s (-((i + 1 : Nat) : Int)) else false) = _
    rw [if_pos (by omega)]; rfl
  | succ t ih =>
    intro i
    rw [R30ProgA.zorb_succ]
    have hneg : -((i + 1 : Nat) : Int) < 0 := by omega
    simp only [Z, hneg, if_true]
    cases i with
    | zero =>
      rw [R30ProgA.zstep_zero, ← ih 1, ← ih 0]
      rw [show -(((0 + 1 : Nat)) : Int) - 1 = -((1 + 1 : Nat) : Int) by omega,
        show -(((0 + 1 : Nat)) : Int) + 1 = 0 by omega, Z_nonneg s t (Int.le_refl 0)]
      simp only [rule, Bool.or_false]
    | succ j =>
      rw [R30ProgA.zstep_succ, ← ih (j + 2), ← ih (j + 1), ← ih j]
      rw [show -(((j + 1 + 1 : Nat)) : Int) - 1 = -((j + 2 + 1 : Nat) : Int) by omega,
        show -(((j + 1 + 1 : Nat)) : Int) + 1 = -((j + 1 : Nat) : Int) by omega]
      rfl

/-- finite on the left -/
def LeftFin (s : Int → Bool) : Prop := ∃ M : Nat, ∀ p : Int, p < -(M : Int) → s p = false

/-- Q_01 in the claim's words, Int positions -/
def Q01I : Prop := ∀ s, LeftFin s → ¬ ∀ k : Nat, Z s (2 * k) (-1) = true

theorem Q01I_iff : Q01I ↔ R30ProgA.Q01 := by
  constructor
  · intro h x ⟨M, hM⟩ hc
    let s : Int → Bool := fun p => if p < 0 then x (-p - 1).toNat else false
    have hsx : (fun i => s (-((i + 1 : Nat) : Int))) = x := by
      funext i; simp only [s]
      rw [if_pos (by omega), show (-(-((i + 1 : Nat) : Int)) - 1).toNat = i by omega]
    refine h s ⟨M, fun p hp => ?_⟩ fun k => ?_
    · simp only [s]; rw [if_pos (by omega)]; exact hM _ (by omega)
    · rw [show (-1 : Int) = -((0 + 1 : Nat) : Int) by rfl, Z_eq, hsx]; exact hc k
  · intro h s ⟨M, hM⟩ hc
    refine h (fun i => s (-((i + 1 : Nat) : Int))) ⟨M, fun i hi => hM _ (by omega)⟩ fun k => ?_
    rw [← Z_eq]; exact hc k

/-- (a) semantic: no finite row has column `-1` equal to `alt f` -/
theorem a_semantic : R30ProgA.Q01 ↔
    ∀ f : Nat → Bool, ¬ ∃ x, R30ProgA.Fin0 x ∧ ∀ t, R30ProgA.zorb x t 0 = R30ProgA.alt f t := by
  rw [R30ProgA.Q01_iff_LR]
  constructor
  · rintro hL f ⟨x, hx, hc⟩
    exact hL f ((R30ProgA.realization _).2 x hc ▸ hx)
  · intro h f hfin
    exact h f ⟨_, hfin, (R30ProgA.realization _).1⟩

/-- (b) semantic: every (possibly infinite) constrained row has a black cell in `[d, d + B)`,
uniformly in the row -/
theorem b_semantic : R30ProgA.Q01 ↔ ∀ d, ∃ B, ∀ x : Nat → Bool,
    (∀ s, R30ProgA.zorb x (2 * s) 0 = true) → ∃ i, d ≤ i ∧ i < d + B ∧ x i = true := by
  rw [R30ProgA.Q01_iff_bounded]
  constructor
  · intro h d
    obtain ⟨B, hB⟩ := h d
    refine ⟨B, fun x hc => ?_⟩
    let f : Nat → Bool := fun s => R30ProgA.zorb x (2 * s + 1) 0
    have hx : ∀ t, R30ProgA.zorb x t 0 = R30ProgA.alt f t := by
      intro t; unfold R30ProgA.alt
      by_cases ht : t % 2 = 0
      · rw [if_pos ht]; have := hc (t / 2); rwa [show 2 * (t / 2) = t by omega] at this
      · rw [if_neg ht]; show _ = R30ProgA.zorb x (2 * (t / 2) + 1) 0
        rw [show 2 * (t / 2) + 1 = t by omega]
    have := (R30ProgA.realization _).2 x hx
    rw [this]; exact hB f
  · intro h d
    obtain ⟨B, hB⟩ := h d
    refine ⟨B, fun f => hB _ fun s => ?_⟩
    rw [(R30ProgA.realization _).1]; simp [R30ProgA.alt]

/-- (d) in Int terms -/
theorem d_int (h : Q01I) : ∀ s, LeftFin s → ¬ ∀ k : Nat, Z s (2 * k + 1) (-1) = true := by
  intro s ⟨M, hM⟩ hc
  have hQ := Q01I_iff.1 h
  refine R30ProgA.Q01_phase1 hQ (fun i => s (-((i + 1 : Nat) : Int))) ⟨M, fun i hi => hM _ (by omega)⟩
    fun k => ?_
  rw [← Z_eq]; exact hc k

/-- (e) against the primitive pattern `cell` -/
theorem e_prim (h : Q01I) : ¬ ∃ T, ∀ t, T ≤ t → cell (t + 2) 0 = cell t 0 :=
  R30ProgA.no_eventual_period_two (Q01I_iff.1 h)

/-- (e) a second way: through the staged module's own theorem -/
theorem e_staged (h : Q01I) : ¬ ∃ T, ∀ t, T ≤ t → Rule30Prize.center (t + 2) = Rule30Prize.center t :=
  Rule30PeriodTwo.not_eventually_period_two_of_Q01 (R30ProgA.Q01_iff_staged.1 (Q01I_iff.1 h))

/-- the center column starts 1,1,0,1,1,1,0,0,1 (A051023) -/
example : (List.range 9).map (fun t => cell t 0) =
    [true, true, false, true, true, true, false, false, true] := by decide

end IndepCheck

#print axioms IndepCheck.Q01I_iff
#print axioms IndepCheck.a_semantic
#print axioms IndepCheck.b_semantic
#print axioms IndepCheck.d_int
#print axioms IndepCheck.e_prim
#print axioms IndepCheck.e_staged
#print axioms Ruliology.CellularAutomata.Rule30Prize.center_not_eventually_constant
#print axioms Ruliology.CellularAutomata.Rule30Jen.not_adjacent
#print axioms Ruliology.CellularAutomata.Rule30Prize.eventually_const_of_mono
#print axioms Ruliology.CellularAutomata.Rule30Prize.no_column_eventually_constant
