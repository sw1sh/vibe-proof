import QTilde.Recurrence

/-!
# The Mantovanelli–Hofstadter recursion is well-defined

Cloitre (arXiv:2604.06237, Theorems 3.5 and 3.6): the slow sequences satisfy (RA) and (RB) for
every `m ≥ 2` (`RA_RB`), and `Q̃(2k + 1) = 2a(k + 1) − 1`, `Q̃(2k) = 2b(k) − 1` then satisfies the
recursion with every recursive argument a positive integer below the current index.

* `qtilde_wellDefined : ∃ Q, IsQTilde Q`, and the sequence is unique (`isQTilde_unique`).
* `Qt_bounds`: `1 ≤ Q̃(n) ≤ n`.
-/

namespace QTilde

/-- (RA) and (RB) for `2 ≤ m ≤ 10`, by computation. -/
theorem RA_RB_small : ∀ m, m < 9 → RA (m + 2) ∧ RB (m + 2) := by
  unfold RA RB
  decide +kernel

/-- Every index `m > 4` lies on some level: `u_r < m ≤ u_{r+1}`. -/
theorem exists_level (m : Nat) (hm : 4 < m) : ∃ r, u r < m ∧ m ≤ u (r + 1) := by
  have key : ∀ k, m ≤ u k → ∃ r, u r < m ∧ m ≤ u (r + 1) := by
    intro k
    induction k with
    | zero => intro h; rw [u_zero] at h; omega
    | succ k ih =>
      intro h
      rcases Nat.lt_or_ge (u k) m with h' | h'
      · exact ⟨k, h', h⟩
      · exact ih h'
  exact key m (by have := u_ge m; omega)

/-- **Cloitre's Theorem 3.5**: (RA) and (RB) hold for every `m ≥ 2`. -/
theorem RA_RB (m : Nat) (hm : 2 ≤ m) : RA m ∧ RB m := by
  rcases Nat.lt_or_ge m 11 with h | h
  · have := RA_RB_small (m - 2) (by omega)
    rwa [show m - 2 + 2 = m by omega] at this
  · obtain ⟨r, h1, h2⟩ := exists_level m (by omega)
    have hus := u_succ r; have hN := lenN r; have hve := v_eq r
    rcases Nat.lt_or_ge (v r) m with hv | hv
    · obtain ⟨t, rfl⟩ : ∃ t, m = v r + (t + 1) := ⟨m - v r - 1, by omega⟩
      exact ⟨RA_neg r t (by omega), RB_neg r t (by omega)⟩
    · cases r with
      | zero => exact absurd hv (by simp [v, ar]; omega)
      | succ r =>
        obtain ⟨t, rfl⟩ : ∃ t, m = u (r + 1) + (t + 1) := ⟨m - u (r + 1) - 1, by omega⟩
        exact ⟨RA_pos r t (by omega), RB_pos r t (by omega)⟩

/-- `1 ≤ a(m), b(m) ≤ m` (Cloitre's Lemma 3.1). -/
theorem bounds (m : Nat) (hm : 1 ≤ m) : 1 ≤ A m ∧ A m ≤ m ∧ 1 ≤ B m ∧ B m ≤ m := by
  rcases Nat.lt_or_ge m 5 with h | h
  · have small : ∀ k, k < 4 → 1 ≤ A (k + 1) ∧ A (k + 1) ≤ k + 1 ∧ 1 ≤ B (k + 1) ∧
        B (k + 1) ≤ k + 1 := by decide +kernel
    have := small (m - 1) (by omega)
    rwa [show m - 1 + 1 = m by omega] at this
  · obtain ⟨r, h1, h2⟩ := exists_level m (by omega)
    have ha := ar_ge_r r; have hve := v_eq r; have hus := u_succ r; have hN := lenN r
    have hu : u r = 2 * ar r - r - 2 := rfl
    rcases Nat.lt_or_ge (v r) m with hv | hv
    · obtain ⟨s, rfl⟩ : ∃ s, m = v r + s := ⟨m - v r, by omega⟩
      rw [A_neg r s (by omega) (by omega), B_neg r s (by omega)]
      have c1 := List.count_le_length (a := false) (l := (N r).take (s - 1))
      have c2 := List.count_le_length (a := true) (l := (N r).take s)
      simp only [List.length_take] at c1 c2
      omega
    · obtain ⟨n, rfl⟩ : ∃ n, m = u r + n := ⟨m - u r, by omega⟩
      rw [A_pos r n (by omega), B_pos r n (by omega)]
      have c1 := List.count_le_length (a := true) (l := (P r).take n)
      have c2 := List.count_le_length (a := false) (l := (P r).take n)
      simp only [List.length_take] at c1 c2
      omega

/-! ### Assembling `Q̃` -/

/-- `Q̃` from the slow sequences: `Q̃(2k + 1) = 2a(k + 1) − 1` and `Q̃(2k) = 2b(k) − 1`. -/
def Qt (n : Nat) : Int :=
  if n % 2 = 1 then 2 * (A ((n + 1) / 2) : Int) - 1 else 2 * (B (n / 2) : Int) - 1

theorem Qt_odd (k : Nat) : Qt (2 * k + 1) = 2 * (A (k + 1) : Int) - 1 := by
  unfold Qt; rw [if_pos (by omega), show (2 * k + 1 + 1) / 2 = k + 1 by omega]

theorem Qt_even (k : Nat) : Qt (2 * k) = 2 * (B k : Int) - 1 := by
  unfold Qt; rw [if_neg (by omega), show 2 * k / 2 = k by omega]

/-- **`Q̃` satisfies the recursion with every argument in range** (Cloitre's Theorem 3.6). -/
theorem isQTilde_Qt : IsQTilde Qt := by
  refine ⟨?_, ?_, fun n hn => ?_⟩
  · rw [show (1 : Nat) = 2 * 0 + 1 from rfl, Qt_odd]; decide
  · rw [show (2 : Nat) = 2 * 1 from rfl, Qt_even]; decide
  · rcases Nat.mod_two_eq_zero_or_one n with hpar | hpar
    · -- `n = 2k`: the recursion is (RB) at `k`
      obtain ⟨k, rfl⟩ : ∃ k, n = 2 * k := ⟨n / 2, by omega⟩
      have hk := bounds k (by omega)
      have hk1 := bounds (k - 1) (by omega)
      have hR := (RA_RB k (by omega)).2
      unfold RB at hR
      refine ⟨2 * (k - A k) + 1, 2 * (k - B (k - 1)) + 1, by omega, by omega, by omega, by omega,
        ?_, ?_, ?_⟩
      · rw [show 2 * k - 1 = 2 * (k - 1) + 1 by omega, Qt_odd, show k - 1 + 1 = k by omega]
        omega
      · rw [show 2 * k - 2 = 2 * (k - 1) by omega, Qt_even]
        omega
      · rw [Qt_even, Qt_odd, Qt_odd, sgn, if_pos (by omega),
          show k - A k + 1 = k + 1 - A k by omega,
          show k - B (k - 1) + 1 = k + 1 - B (k - 1) by omega]
        omega
    · -- `n = 2k + 1`: the recursion is (RA) at `k + 1`
      obtain ⟨k, rfl⟩ : ∃ k, n = 2 * k + 1 := ⟨n / 2, by omega⟩
      have hk := bounds k (by omega)
      have hR := (RA_RB (k + 1) (by omega)).1
      unfold RA at hR
      rw [show k + 1 - 1 = k by omega] at hR
      refine ⟨2 * (k + 1 - B k), 2 * (k + 1 - A k), by omega, by omega, by omega, by omega,
        ?_, ?_, ?_⟩
      · rw [show 2 * k + 1 - 1 = 2 * k by omega, Qt_even]
        omega
      · rw [show 2 * k + 1 - 2 = 2 * (k - 1) + 1 by omega, Qt_odd, show k - 1 + 1 = k by omega]
        omega
      · rw [Qt_odd, Qt_even, Qt_even, sgn, if_neg (by omega)]
        omega

/-- **The Mantovanelli–Hofstadter recursion is well-defined**: there is a sequence satisfying
`Q̃(1) = Q̃(2) = 1` and `Q̃(n) = Q̃(n − Q̃(n − 1)) + Q̃(n − Q̃(n − 2)) + (−1)ⁿ` for all `n ≥ 3`, with
every recursive argument in `[1, n − 1]`. By `isQTilde_unique` it is unique. -/
theorem qtilde_wellDefined : ∃ Q, IsQTilde Q := ⟨Qt, isQTilde_Qt⟩

/-- `1 ≤ Q̃(n) ≤ n` (Cloitre's Theorem 3.6). -/
theorem Qt_bounds (n : Nat) (hn : 1 ≤ n) : 1 ≤ Qt n ∧ Qt n ≤ n := by
  rcases Nat.mod_two_eq_zero_or_one n with hpar | hpar
  · obtain ⟨k, rfl⟩ : ∃ k, n = 2 * k := ⟨n / 2, by omega⟩
    have := bounds k (by omega)
    rw [Qt_even]; omega
  · obtain ⟨k, rfl⟩ : ∃ k, n = 2 * k + 1 := ⟨n / 2, by omega⟩
    have := bounds (k + 1) (by omega)
    rw [Qt_odd]; omega

end QTilde
