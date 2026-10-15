import Rule30Equivalents
import Ruliology.CellularAutomata.Rule30Realization
import Ruliology.CellularAutomata.Rule30Diagonals
import Ruliology.CellularAutomata.Rule30DrivenLeft
import Ruliology.CellularAutomata.Rule30Ether
import Ruliology.CellularAutomata.Rule30StripCertificates
import Mathlib.ModelTheory.Arithmetic.Presburger.Definability
import Mathlib.Computability.MyhillNerode
import Mathlib.Computability.ContextFreeGrammar
import Mathlib.Dynamics.OmegaLimit
import Mathlib.Dynamics.SymbolicDynamics.Basic
import Mathlib.Data.Nat.Nth
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Dioph

/-! Merged-catalog scratch file 1/3: statements of the equivalent forms of Rule 30 Problem 1 that
need no real analysis. Each statement either *is* a library theorem (checked by `:=` to it) or is
stated with `sorry`. Nothing here is a proof of anything new; the file checks names and types. -/

open Ruliology.CellularAutomata

namespace Catalog

/-! ## A. Bookkeeping -/

namespace FC
/-- google-deepmind/formal-conjectures `Rule30.step`, copied verbatim. -/
def step (row : ℤ → Bool) : ℤ → Bool := fun i => xor (row (i - 1)) (row i || row (i + 1))
/-- formal-conjectures `Rule30.state`. -/
def state : ℕ → ℤ → Bool
  | 0 => fun i => decide (i = 0)
  | t + 1 => step (state t)
/-- formal-conjectures `Rule30.centerColumn`. -/
def centerColumn (t : ℕ) : Bool := state t 0

theorem problem1_iff_fc : Rule30Prize.Problem1 ↔
    ¬ ∃ p : ℕ, 0 < p ∧ ∃ N : ℕ, ∀ t : ℕ, N ≤ t → centerColumn (t + p) = centerColumn t := sorry

theorem problem1_iff_wolfram : Rule30Prize.Problem1 ↔
    ¬ ∃ p i : ℕ, 0 < p ∧ ∀ t, i < t → Rule30Prize.center (t + p) = Rule30Prize.center t := sorry
end FC

theorem problem1_iff_no_word : Rule30Prize.Problem1 ↔
    ∀ w : List Bool, w ≠ [] → ¬ Rule30StripCertificates.EventuallyWord w :=
  Rule30StripCertificates.problem1_iff_no_word

theorem problem1_iff_pi2 : Rule30Prize.Problem1 ↔
    ∀ T P : ℕ, 0 < P → ∃ t, T ≤ t ∧ Rule30Prize.center (t + P) ≠ Rule30Prize.center t := sorry

theorem problem1_iff_factorial_periods : Rule30Prize.Problem1 ↔
    ∀ k : ℕ, ¬ ∃ T, ∀ t, T ≤ t →
      Rule30Prize.center (t + (k + 1).factorial) = Rule30Prize.center t := sorry

/-- The black times of the center column form a Diophantine set (a consequence of DPRM; open as a
formal target). Together with `problem1_iff_pi2` this is the Diophantine form of Problem 1. -/
theorem center_dioph : Dioph {v : Fin 1 → ℕ | Rule30Prize.center (v 0) = true} := sorry

/-- NKS p. 871 / OEIS A110240: rows as integers, `a(t+1) = a(t) xor (2 a(t) or 4 a(t))`. -/
def nksRow : ℕ → ℕ
  | 0 => 1
  | t + 1 => let a := nksRow t; a ^^^ (2 * a ||| 4 * a)

theorem problem1_iff_nksRow : Rule30Prize.Problem1 ↔
    ¬ Rule30Jen.EventuallyPeriodic (fun t => (nksRow t).testBit t) := sorry

/-- The right-diagonal array `A j t = cell t (t - j)`, by its own recurrence (Rule30Diagonals). -/
def diagArray : ℕ → ℕ → Bool
  | 0, _ => true
  | 1, t => decide (t % 2 = 1)
  | _ + 2, 0 => false
  | j + 2, t + 1 => xor (diagArray (j + 2) t) (diagArray (j + 1) t || diagArray j t)

theorem problem1_iff_diagArray : Rule30Prize.Problem1 ↔
    ¬ Rule30Jen.EventuallyPeriodic (fun t => diagArray t t) := sorry

/-! ## B. Cellular-automaton structure -/

theorem problem1_iff_rule86 : Rule30Prize.Problem1 ↔
    ¬ Rule30Equivalents.EventuallyPeriodic
      (fun t => Rule30Equivalents.Symmetry.evolve 86 Rule30Equivalents.Symmetry.blackSeed t 0) :=
  Rule30Equivalents.Symmetry.problem1_iff_rule86

theorem problem1_iff_rule135 : Rule30Prize.Problem1 ↔
    ¬ Rule30Equivalents.EventuallyPeriodic
      (fun t => Rule30Equivalents.Symmetry.evolve 135 Rule30Equivalents.Symmetry.whiteSeed t 0) :=
  Rule30Equivalents.Symmetry.problem1_iff_rule135

theorem problem1_iff_rule149 : Rule30Prize.Problem1 ↔
    ¬ Rule30Equivalents.EventuallyPeriodic
      (fun t => Rule30Equivalents.Symmetry.evolve 149 Rule30Equivalents.Symmetry.whiteSeed t 0) :=
  Rule30Equivalents.Symmetry.problem1_iff_rule149

/-- The stripe seeds `1, 11, 101, 1011, 10101, …`. -/
def stripeSeed (n : ℕ) (p : ℤ) : Bool := decide (0 ≤ p ∧ p < n ∧ p % 2 = 0) || decide (p = n)

theorem problem1_iff_stripeSeed (n : ℕ) : Rule30Prize.Problem1 ↔
    ¬ Rule30Jen.EventuallyPeriodic (fun t => Rule30Realization.evol (stripeSeed n) t 0) := sorry

theorem problem1_iff_realization : Rule30Prize.Problem1 ↔
    ∀ u : ℕ → Bool, Rule30Jen.EventuallyPeriodic u →
      Rule30Realization.conf Rule30Realization.seed u ≠ Rule30Realization.seed := sorry

theorem problem1_iff_coupled_halves : Rule30Prize.Problem1 ↔
    ∀ u : ℕ → Bool, u 0 = true →
      (∀ t, u (t + 1) = Rule30Jen.rule (Rule30DrivenLeft.L u (fun _ => false) t (-1)) (u t)
        (Rule30Ether.drv u (fun _ => false) t 1)) →
      ¬ Rule30Jen.EventuallyPeriodic u := sorry

/-! ## F. Words and symbolic dynamics -/

theorem problem1_iff_infinite_shifts : Rule30Prize.Problem1 ↔
    (Set.range (fun n : ℕ => fun t => Rule30Prize.center (n + t))).Infinite :=
  Rule30Equivalents.ShiftOrbit.problem1_iff_infinite_shifts

theorem problem1_iff_not_preperiodic : Rule30Prize.Problem1 ↔
    ∀ m, Rule30Equivalents.ShiftOrbit.shift^[m] Rule30Prize.center ∉
      Function.periodicPts Rule30Equivalents.ShiftOrbit.shift :=
  Rule30Equivalents.ShiftOrbit.problem1_iff_not_preperiodic

theorem problem1_iff_injective_fullShift : Rule30Prize.Problem1 ↔
    Function.Injective (fun n : ℕ => SymbolicDynamics.FullShift.shift n Rule30Prize.center) := sorry

theorem problem1_iff_ncard_factors : Rule30Prize.Problem1 ↔
    ∀ n, n + 1 ≤ (Rule30Equivalents.ShiftOrbit.factors Rule30Prize.center n).ncard :=
  Rule30Equivalents.ShiftOrbit.problem1_iff_ncard_factors

theorem problem1_iff_prefix_certificates : Rule30Prize.Problem1 ↔
    ∀ N : ℕ, ∃ n M : ℕ, N < ((Finset.range M).image
      fun i => List.ofFn fun j : Fin n => Rule30Prize.center (i + j)).card := sorry

theorem problem1_iff_orbit_closure_infinite : Rule30Prize.Problem1 ↔
    (closure (Set.range fun n : ℕ => fun t => Rule30Prize.center (n + t))).Infinite := sorry

theorem problem1_iff_omegaLimit_infinite : Rule30Prize.Problem1 ↔
    (omegaLimit Filter.atTop (fun (n : ℕ) (x : ℕ → Bool) => fun t => x (n + t))
      {Rule30Prize.center}).Infinite := sorry

/-- `w` occurs in the center column, followed by the letter `a`. -/
def OccursThen (w : List Bool) (a : Bool) : Prop :=
  ∃ i : ℕ, (∀ j : Fin w.length, Rule30Prize.center (i + (j : ℕ)) = w.get j) ∧
    Rule30Prize.center (i + w.length) = a

theorem problem1_iff_right_special : Rule30Prize.Problem1 ↔
    ∀ n, ∃ w : List Bool, w.length = n ∧ OccursThen w false ∧ OccursThen w true := sorry

/-- The tail language: words of length `n` occurring infinitely often. -/
def tailFactors (n : ℕ) : Set (Fin n → Bool) :=
  {w | ∀ N, ∃ i : ℕ, N ≤ i ∧ ∀ j : Fin n, Rule30Prize.center (i + (j : ℕ)) = w j}

theorem problem1_iff_tail_complexity : Rule30Prize.Problem1 ↔
    ∀ n, n + 1 ≤ (tailFactors n).ncard := sorry

theorem problem1_iff_shifted (k : ℕ) : Rule30Prize.Problem1 ↔
    ¬ Rule30Jen.EventuallyPeriodic (fun t => Rule30Prize.center (t + k)) := sorry

theorem problem1_iff_complement : Rule30Prize.Problem1 ↔
    ¬ Rule30Equivalents.EventuallyPeriodic (fun t => !Rule30Prize.center t) :=
  Rule30Equivalents.Symmetry.problem1_iff_complement

theorem problem1_iff_xor_derivative : Rule30Prize.Problem1 ↔
    ¬ Rule30Jen.EventuallyPeriodic
      (fun t => xor (Rule30Prize.center t) (Rule30Prize.center (t + 1))) := sorry

theorem problem1_iff_running_parity : Rule30Prize.Problem1 ↔
    ¬ Rule30Jen.EventuallyPeriodic
      (fun t => ((List.range (t + 1)).map Rule30Prize.center).foldl xor false) := sorry

theorem problem1_iff_decimation (k : ℕ) (hk : 0 < k) : Rule30Prize.Problem1 ↔
    ∃ r < k, ¬ Rule30Jen.EventuallyPeriodic (fun n => Rule30Prize.center (k * n + r)) := sorry

theorem problem1_iff_nonconstant_class : Rule30Prize.Problem1 ↔
    ∀ P, 0 < P → ∃ r < P, ¬ ∃ K b, ∀ k, K ≤ k → Rule30Prize.center (r + k * P) = b := sorry

/-- Gaps between consecutive black cells of the center column. -/
noncomputable def blackGap (n : ℕ) : ℕ :=
  Nat.nth (fun t => Rule30Prize.center t = true) (n + 1) -
    Nat.nth (fun t => Rule30Prize.center t = true) n

theorem problem1_iff_black_gaps : Rule30Prize.Problem1 ↔
    ¬ ∃ T P, 0 < P ∧ ∀ n, T ≤ n → blackGap (n + P) = blackGap n := sorry

/-- Lengths of the runs of equal colors (from the second run on). -/
noncomputable def runLength (k : ℕ) : ℕ :=
  Nat.nth (fun t => Rule30Prize.center t ≠ Rule30Prize.center (t + 1)) (k + 1) -
    Nat.nth (fun t => Rule30Prize.center t ≠ Rule30Prize.center (t + 1)) k

theorem problem1_iff_run_lengths : Rule30Prize.Problem1 ↔
    ¬ ∃ T P, 0 < P ∧ ∀ k, T ≤ k → runLength (k + P) = runLength k := sorry

/-! ## G. Logic, automata and computation -/

theorem problem1_iff_not_presburger (A : Set ℕ) : Rule30Prize.Problem1 ↔
    ¬ A.Definable₁ FirstOrder.Language.presburger {t | Rule30Prize.center t = true} := sorry

theorem problem1_iff_not_semilinear : Rule30Prize.Problem1 ↔
    ¬ IsSemilinearSet {t : ℕ | Rule30Prize.center t = true} := sorry

/-- `{1ⁿ : c(n) = 1}` over a one-letter alphabet. -/
def unaryLang : Language Unit := {l | Rule30Prize.center l.length = true}

theorem problem1_iff_unary_not_regular : Rule30Prize.Problem1 ↔ ¬ unaryLang.IsRegular := sorry

theorem problem1_iff_unary_not_contextFree : Rule30Prize.Problem1 ↔
    ¬ unaryLang.IsContextFree := sorry

/-- The prefixes `c(0) c(1) … c(n-1)`. -/
def prefixLang : Language Bool := {l | l = (List.range l.length).map Rule30Prize.center}

theorem problem1_iff_prefixes_not_regular : Rule30Prize.Problem1 ↔ ¬ prefixLang.IsRegular := sorry

theorem problem1_iff_prefixes_not_contextFree : Rule30Prize.Problem1 ↔
    ¬ prefixLang.IsContextFree := sorry

/-- A nondeterministic Büchi automaton over the alphabet `α`. -/
structure Buchi (α : Type) where
  Q : Type
  [fin : Finite Q]
  init : Q
  step : Q → α → Q → Prop
  acc : Set Q

/-- `B` has an accepting run on `w`: it visits `acc` infinitely often. -/
def Buchi.Accepts {α : Type} (B : Buchi α) (w : ℕ → α) : Prop :=
  ∃ r : ℕ → B.Q, r 0 = B.init ∧ (∀ n, B.step (r n) (w n) (r (n + 1))) ∧
    ∀ N, ∃ n, N ≤ n ∧ r n ∈ B.acc

theorem problem1_iff_not_omega_regular : Rule30Prize.Problem1 ↔
    ¬ ∃ B : Buchi Bool, ∀ w, B.Accepts w ↔ w = Rule30Prize.center := sorry

/-- State of a finite-state reader after reading `c(0) … c(n-1)`. -/
def readState {σ : Type} (s₀ : σ) (δ : σ → Bool → σ) : ℕ → σ
  | 0 => s₀
  | n + 1 => δ (readState s₀ δ n) (Rule30Prize.center n)

theorem problem1_iff_unpredictable : Rule30Prize.Problem1 ↔
    ∀ (σ : Type) [Finite σ] (s₀ : σ) (δ : σ → Bool → σ) (g : σ → Bool),
      ∀ N, ∃ n, N ≤ n ∧ g (readState s₀ δ n) ≠ Rule30Prize.center n := sorry

theorem problem1_iff_no_finite_generator : Rule30Prize.Problem1 ↔
    ¬ ∃ (σ : Type) (_ : Finite σ) (s₀ : σ) (F : σ → σ) (g : σ → Bool) (T : ℕ),
      ∀ t, T ≤ t → Rule30Prize.center t = g (F^[t] s₀) := sorry

theorem problem1_iff_no_nlfsr : Rule30Prize.Problem1 ↔
    ∀ m : ℕ, ¬ ∃ F : (Fin m → Bool) → Bool,
      ∀ i, Rule30Prize.center (i + m) = F (fun k => Rule30Prize.center (i + k)) := sorry

/-- A Lempel–Ziv (1976) history of the prefix of length `n`: cut points `0 = b₀ < … < b_k = n`;
each component, minus its last letter, is copied from an earlier start (overlap allowed). -/
def IsLZHistory (n : ℕ) (b : List ℕ) : Prop :=
  b.head? = some 0 ∧ b.getLast? = some n ∧ List.IsChain (· < ·) b ∧
    ∀ p ∈ b.zip b.tail, p.2 = p.1 + 1 ∨ ∃ s < p.1, ∀ j, p.1 + j + 1 < p.2 →
      Rule30Prize.center (s + j) = Rule30Prize.center (p.1 + j)

/-- LZ76 complexity: the fewest components of a history (Lempel–Ziv: the exhaustive history
attains it). -/
noncomputable def lzComplexity (n : ℕ) : ℕ := sInf {k | ∃ b, IsLZHistory n b ∧ b.length = k + 1}

theorem problem1_iff_lz_unbounded : Rule30Prize.Problem1 ↔ ∀ K, ∃ n, K < lzComplexity n := sorry

/-- The `k`-kernel `{n ↦ f(kᵉ n + r) : r < kᵉ}`. -/
def kernel (k : ℕ) (f : ℕ → Bool) : Set (ℕ → Bool) :=
  {g | ∃ e r, r < k ^ e ∧ g = fun n => f (k ^ e * n + r)}

/-- `k`-automatic, by Eilenberg's kernel criterion. -/
def IsAutomatic (k : ℕ) (f : ℕ → Bool) : Prop := (kernel k f).Finite

theorem problem1_iff_not_two_three_automatic : Rule30Prize.Problem1 ↔
    ¬ (IsAutomatic 2 Rule30Prize.center ∧ IsAutomatic 3 Rule30Prize.center) := sorry

end Catalog
