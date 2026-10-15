import P3Ether
import P3NoWall
import P3Trap001
import P3Reach
import P3Left
import P3Skel

/-! Verifier's restatements: each `example` gives the type in the verifier's own words, with the
worker's definitions unfolded where it matters, and closes it with the worker's theorem. -/

open Ruliology.CellularAutomata
open Ruliology.CellularAutomata.Rule30EtherThree

/-! ### Base definitions are rule 30 -/
example : ∀ a b c : Bool, Rule30Jen.rule a b c = xor a (b || c) := fun _ _ _ => rfl
example : ∀ p : Int, Rule30Jen.cell 0 p = decide (p = 0) := fun _ => rfl
example : ∀ (t : Nat) (p : Int), Rule30Jen.cell (t + 1) p =
    xor (Rule30Jen.cell t (p - 1)) (Rule30Jen.cell t p || Rule30Jen.cell t (p + 1)) := fun _ _ => rfl
example : ∀ t p : Nat, Rule30Ether.trueRight t p = Rule30Jen.cell t (p : Int) := fun _ _ => rfl
example (c x : Nat → Bool) (t p : Nat) :
    Rule30Ether.drv c x (t + 1) (p + 1) =
      xor (Rule30Ether.drv c x t p) (Rule30Ether.drv c x t (p + 1) || Rule30Ether.drv c x t (p + 2)) := rfl
example (c x : Nat → Bool) (t : Nat) : Rule30Ether.drv c x (t + 1) 0 = c (t + 1) := rfl
example (c x : Nat → Bool) (p : Nat) : Rule30Ether.drv c x 0 (p + 1) = x (p + 1) := rfl
example (c : Nat → Bool) (s : Int → Bool) (t : Nat) (p : Int) (hp : p < 0) :
    Rule30DrivenLeft.L c s (t + 1) p =
      xor (Rule30DrivenLeft.L c s t (p - 1)) (Rule30DrivenLeft.L c s t p || Rule30DrivenLeft.L c s t (p + 1)) :=
  Rule30DrivenLeft.L_succ hp
example (c : Nat → Bool) (s : Int → Bool) (p : Int) (hp : p < 0) : Rule30DrivenLeft.L c s 0 p = s p :=
  Rule30DrivenLeft.L_zero hp
example (c : Nat → Bool) (s : Int → Bool) (t : Nat) : Rule30DrivenLeft.L c s t 0 = c t :=
  Rule30DrivenLeft.L_col0 t

/-! ### Ether -/
example : ether3Table =
    [[false, false, true], [false, false, true], [false, true, true], [true, true, false],
     [false, true, false], [false, true, false], [true, true, false], [true, false, true],
     [true, false, false], [true, false, false], [true, false, true], [false, true, true]] := rfl
example : ∀ j φ : Nat, ether3 j φ = (ether3Table.getD (j % 12) []).getD (φ % 3) false := fun _ _ => rfl
example : ∀ j φ : Nat, ether3 j (φ + 1) = xor (ether3 (j + 11) φ) (ether3 j φ || ether3 (j + 1) φ) :=
  ether3_rule
example : ∀ j φ : Nat, ether3 (j + 4) φ = ether3 j (φ + 1) := ether3_glide
example (w : List Bool) (j0 s : Nat) :
    aligned3 w j0 s = (List.range 3).all (fun ψ => ether3 j0 (ψ + s) == w.getD (ψ % 3) false) := rfl
example : ∀ j0, j0 < 12 → ∀ s, s < 3 →
    (aligned3 [false, false, true] j0 s = true ↔
      (j0, s) ∈ [(0, 0), (1, 0), (4, 2), (5, 2), (8, 1), (9, 1)]) := alignments_001_complete
example : ∀ j0, j0 < 12 → ∀ s, s < 3 →
    (aligned3 [false, true, true] j0 s = true ↔
      (j0, s) ∈ [(2, 0), (3, 2), (6, 2), (7, 1), (10, 1), (11, 0)]) := alignments_011_complete

/-! ### Walls -/
example (a b : Nat) (W : Nat → Nat → Prop) : WallOK a b W ↔
    ((∀ φ r, W φ r → r < 2 ^ b) ∧
     (∀ φ r, W φ r → ether3 a φ = false → r.testBit 0 = ether3 (a + 1) φ) ∧
     (∀ φ r (z : Bool), W φ r →
        W ((φ + 1) % 3) (Rule30StripCertificates.stripStep b (ether3 a φ) z r))) := Iff.rfl
example (F : Nat → Nat → Bool) (b t k r : Nat) :
    EncF F b t k r ↔ (r < 2 ^ b ∧ ∀ i, i < b → r.testBit i = F t (k + 1 + i)) := Iff.rfl
example : ∀ (a b : Nat), 0 < b → b ≤ 12 → ∀ {W : Nat → Nat → Prop}, WallOK a b W → ∀ φ r, ¬ W φ r :=
  fun a b hb hb12 _ hW => no_wall_le_12 a b hb hb12 hW
example : ∀ {F : Nat → Nat → Bool}, Rule30Ether.IsR30 F → ∀ {a b : Nat} {W : Nat → Nat → Prop},
    WallOK a b W → 0 < b → ∀ (j0 s k t1 : Nat), (j0 + k) % 12 = a % 12 →
    (∀ t, t1 ≤ t → F t 0 = ether3 j0 (t + s)) →
    (∀ p, 1 ≤ p → p ≤ k → F t1 p = ether3 (j0 + p) (t1 + s)) →
    ∀ (r : Nat), EncF F b t1 k r → W ((t1 + s) % 3) r →
    ∀ n, (∀ p, p ≤ k → F (t1 + n) p = ether3 (j0 + p) (t1 + n + s)) ∧
      ∃ r', EncF F b (t1 + n) k r' ∧ W ((t1 + n + s) % 3) r' :=
  fun hF _ _ _ hW hb => trap_invariant3 hF hW hb
example : ∀ {a b : Nat} {W : Nat → Nat → Prop}, WallOK a b W → 0 < b →
    ∀ (T t1 j0 s k : Nat), (j0 + k) % 12 = a % 12 →
    (∀ t, T ≤ t → Rule30Jen.cell t 0 = ether3 j0 (t - T + s)) → T ≤ t1 →
    (∀ p : Nat, 1 ≤ p → p ≤ k → Rule30Jen.cell t1 (p : Int) = ether3 (j0 + p) (t1 - T + s)) →
    ∀ (r : Nat), EncF Rule30Ether.trueRight b t1 k r → W ((t1 - T + s) % 3) r → False :=
  fun hW hb => ether_wall_trap3 hW hb
example : ∀ (w : List Bool) (A : List (Nat × Nat)), (∀ al ∈ A, aligned3 w al.1 al.2 = true) →
    ∀ {a b : Nat} {W : Nat → Nat → Prop}, WallOK a b W → 0 < b →
    (∀ (x : Nat → Bool) (n : Nat), (∀ p, n < p → x p = false) → ∀ φ : Nat,
      ∃ al ∈ A, ∃ t1, ∃ k r, (al.1 + k) % 12 = a % 12 ∧
        (∀ p, 1 ≤ p → p ≤ k → Rule30Ether.drv (fun t => wordAt3 w (t + φ)) x t1 p = ether3 (al.1 + p) (t1 + (al.2 + φ))) ∧
        EncF (Rule30Ether.drv (fun t => wordAt3 w (t + φ)) x) b t1 k r ∧ W ((t1 + (al.2 + φ)) % 3) r) →
    ¬ ∃ T, ∀ t, T ≤ t → Rule30Jen.cell t 0 = w.getD ((t - T) % 3) false :=
  fun w A hal _ _ _ hW hb hA => absorption3_excludes w A hal hW hb hA

/-! ### The 001 trap -/
example : t001.w = [false, false, true] ∧ t001.b = 47 ∧ t001.m = 21 ∧ t001.n = 815 ∧
    t001.lb = 5 ∧ t001.ib = 10 := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
example : PTrap.check t001 = true := t001_check
example (C : PTrap) : C.check = (decide (0 < C.m) && decide (C.m % 3 = 0) && allBelowT C.nodeOK C.n) := rfl
example (C : PTrap) (i : Nat) : C.nodeOK i =
    (decide (C.lab i < C.m) &&
      (wordAt3 C.w (C.lab i % 3) || ((C.st i).testBit 0 == C.u.testBit (C.lab i))) &&
      C.edgeOK i false && C.edgeOK i true) := rfl
example (C : PTrap) (i : Nat) (z : Bool) : C.edgeOK i z =
    (decide (C.nxt i z < C.n) &&
      (C.st (C.nxt i z) == Rule30StripCertificates.stripStep C.b (wordAt3 C.w (C.lab i % 3)) z (C.st i)) &&
      (C.lab (C.nxt i z) == (C.lab i + 1) % C.m)) := rfl
example : ∀ (T : Nat), (∀ t, T ≤ t → Rule30Jen.cell t 0 = [false, false, true].getD ((t - T) % 3) false) →
    ∀ (t1 i : Nat), T ≤ t1 → i < 815 → (t1 - T) % 3 = t001.lab i % 3 →
    (t001.st i < 2 ^ 47 ∧ ∀ j, j < 47 → (t001.st i).testBit j = Rule30Jen.cell t1 ((0 + 1 + j : Nat) : Int)) → False :=
  fun T hc t1 i ht1 hi hph hr => trap_001 T hc t1 i ht1 hi hph hr
example : AbsorptionT t001 ↔
    ∀ (x : Nat → Bool) (n : Nat), (∀ p, n < p → x p = false) → ∀ φ : Nat,
      ∃ t1 i, i < 815 ∧ (t1 + φ) % 3 = t001.lab i % 3 ∧
        EncF (Rule30Ether.drv (fun t => [false, false, true].getD ((t + φ) % 3) false) x) 47 t1 0 (t001.st i) :=
  Iff.rfl
example : AbsorptionT t001 → ¬ ∃ T, ∀ t, T ≤ t → Rule30Jen.cell t 0 = [false, false, true].getD ((t - T) % 3) false :=
  not_eventually_001_of_absorption
example : ∃ i, i < 815 ∧ (1270 + 0) % 3 = t001.lab i % 3 ∧
    EncF (Rule30Ether.drv (fun t => [false, false, true].getD ((t + 0) % 3) false) (fun _ => false)) 47 1270 0
      (t001.st i) := t001_reached

/-! ### Left side -/
example : ∀ (T : Nat), (∀ t, T ≤ t → Rule30Jen.cell t 0 = [false, false, true].getD ((t - T) % 3) false) →
    ∀ t, T ≤ t →
    ((t - T) % 3 = 0 → Rule30Jen.cell t (-1) = Rule30Jen.cell t 1) ∧
    ((t - T) % 3 = 1 → Rule30Jen.cell t (-1) = !Rule30Jen.cell t 1) ∧
    ((t - T) % 3 = 2 → Rule30Jen.cell t (-1) = true) := col_m1_001
example : ∀ (T : Nat), (∀ t, T ≤ t → Rule30Jen.cell t 0 = [false, true, true].getD ((t - T) % 3) false) →
    ∀ t, T ≤ t →
    ((t - T) % 3 = 0 → Rule30Jen.cell t (-1) = !Rule30Jen.cell t 1) ∧
    ((t - T) % 3 = 1 → Rule30Jen.cell t (-1) = false) ∧
    ((t - T) % 3 = 2 → Rule30Jen.cell t (-1) = true) := col_m1_011
example : Q001 ↔ ∀ (m : Nat) (s : Int → Bool), 0 < m → (∀ p : Int, p < -(m : Int) → s p = false) →
    s (-(m : Int)) = true → ¬ ∀ k, Rule30DrivenLeft.L (fun _ => false) s (3 * k) (-1) = true := Iff.rfl
example : Q001 → ¬ ∃ T, ∀ t, T ≤ t → Rule30Jen.cell t 0 = [false, false, true].getD ((t - T) % 3) false :=
  not_eventually_001_of_Q001
example : Rule30PeriodTwo.stripe = fun p : Int => decide (p % 2 = 1) := rfl
example : ∀ k : Nat, Rule30DrivenLeft.L (fun _ => false) Rule30PeriodTwo.stripe (3 * k) (-1) = true := Q001_stripe
example : effWord3 w011 = [false, true, false] := effWord3_011
example : effWord3 w001 = [false, false, false] := effWord3_001
example : colPattern3 w011 = [none, some false, some true] := rfl
example (P : List (Option Bool)) (φ : Nat) (b : Bool) :
    fits3 P φ b = (match P.getD φ none with | none => true | some v => b == v) := rfl
example : C3w w011 ↔ ∀ s : Int → Bool, (∃ M : Nat, ∀ p : Int, p < -(M : Int) → s p = false) →
    ¬ ∃ K, ∀ k, K ≤ k → fits3 [none, some false, some true] (k % 3)
      (Rule30DrivenLeft.L (fun k => wordAt3 (effWord3 w011) k) s k (-1)) = true := Iff.rfl
example : C3w w011 → ¬ ∃ T, ∀ t, T ≤ t → Rule30Jen.cell t 0 = [false, true, true].getD ((t - T) % 3) false :=
  not_eventually_011_of_C3w
example : etherLeft = fun p : Int => ether3 (((p + 2) % 12).toNat) 0 := rfl
example : ∀ k : Nat, fits3 [none, some false, some true] (k % 3)
    (Rule30DrivenLeft.L (fun k => wordAt3 (effWord3 w011) k) etherLeft k (-1)) = true := C3w_011_ether

/-! ### Skeletons -/
example : ∀ (T : Nat), (∀ t, T ≤ t → Rule30Jen.cell t 0 = [false, false, true].getD ((t - T) % 3) false) →
    ∃ T', T ≤ T' ∧ ∀ t, T' ≤ t → (t - T) % 3 = 0 → Rule30Jen.cell t 1 = false := skeleton_001
example : ∀ (T : Nat), (∀ t, T ≤ t → Rule30Jen.cell t 0 = [false, true, true].getD ((t - T) % 3) false) →
    ∃ T', T ≤ T' ∧ ∀ t, T' ≤ t →
      ((t - T) % 3 = 1 → Rule30Jen.cell t 1 = true) ∧ ((t - T) % 3 = 2 → Rule30Jen.cell t 1 = false) :=
  skeleton_011
example : ∀ (T : Nat), (∀ t, T ≤ t → Rule30Jen.cell t 0 = [false, false, true].getD ((t - T) % 3) false) →
    ∃ T', T ≤ T' ∧ ∀ t, T' ≤ t →
      ((t - T) % 3 = 0 → Rule30Jen.cell t (-1) = false) ∧
      ((t - T) % 3 = 1 → Rule30Jen.cell t (-1) = !Rule30Jen.cell t 1) ∧
      ((t - T) % 3 = 2 → Rule30Jen.cell t (-1) = true) := col_m1_001_skeleton
example : C3s001 ↔ ∀ s : Int → Bool, (∃ M : Nat, ∀ p : Int, p < -(M : Int) → s p = false) →
    ¬ ∃ K, ∀ k, K ≤ k → fits3 [some false, none, some true] (k % 3)
      (Rule30DrivenLeft.L (fun _ => false) s k (-1)) = true := Iff.rfl
example : C3s001 → ¬ ∃ T, ∀ t, T ≤ t → Rule30Jen.cell t 0 = [false, false, true].getD ((t - T) % 3) false :=
  not_eventually_001_of_C3s

/-! ### Least period 3 means a tail 001 or 011 up to rotation (the worker's untformalized step):
the three rotations of each word are the same tail with a different start, so the two words suffice. -/
example : ∀ ψ, wordAt3 [false, false, true] (ψ + 1) = wordAt3 [false, true, false] ψ := by
  intro ψ; unfold wordAt3; have : ψ % 3 = 0 ∨ ψ % 3 = 1 ∨ ψ % 3 = 2 := by omega
  rcases this with h | h | h <;> simp [show (ψ + 1) % 3 = (ψ % 3 + 1) % 3 by omega, h]
