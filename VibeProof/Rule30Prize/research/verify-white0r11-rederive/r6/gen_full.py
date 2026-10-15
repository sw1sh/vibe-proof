# Generate R6Full.lean: Lean proof (bv_decide + kernel-checked linking) that the center column of rule 30
# is not eventually periodic with repeating word 0^6 11.
import sys
out = sys.argv[1]
w = '00000011'; Q = 16; ns = list(range(33, 41))
link = open('/Users/swish/.claude/jobs/b8cd2926/tmp/r30prize/verify-white0r11-rederive/r6/Link.lean').read()
link = link.replace('end R30W6', '')
L = [link, 'set_option maxHeartbeats 0', '']
for n in ns:
    N = n + Q; W = N + 1
    args = ' '.join(f"r{t}" for t in range(N + 1))
    L.append(f"theorem forced_{n} ({args} : BitVec {W})")
    for t in range(N):
        d = w[t % 8]
        L.append(f"    (h{t + 1} : r{t + 1} = ((r{t} <<< 1) ||| {d}#{W}) ^^^ (r{t} ||| (r{t} >>> 1)))")
    L.append(f"    : r{n}.getLsbD 0 = r{N}.getLsbD 0 := by")
    L.append("  bv_decide")
    L.append("")
    margs = ' '.join(f"(model a {W} {t})" for t in range(N + 1))
    rfls = ' '.join('rfl' for _ in range(N))
    L.append(f"theorem model_forced_{n} (a : Nat) : (model a {W} {n}).getLsbD 0 = (model a {W} {N}).getLsbD 0 :=")
    L.append(f"  forced_{n} {margs}")
    L.append(f"    {rfls}")
    L.append("")
    L.append(f"theorem col1_forced_{n} (a : Nat) (hd : ∀ t, cell (a + t) 0 = drv t) :")
    L.append(f"    cell (a + {n}) 1 = cell (a + {N}) 1 := by")
    L.append(f"  have e := model_forced_{n} a")
    L.append(f"  rw [model_bit a {W} hd {n} 0 (by omega), model_bit a {W} hd {N} 0 (by omega)] at e")
    L.append(f"  exact e")
    L.append("")
cases = ' | '.join('h' for _ in ns)
L.append(f"""theorem col1_forced (a n : Nat) (hd : ∀ t, cell (a + t) 0 = drv t) (h1 : 33 ≤ n) (h2 : n < 41) :
    cell (a + n) 1 = cell (a + n + 16) 1 := by
  rcases (show {' ∨ '.join(f'n = {n}' for n in ns)} by omega) with {cases}
""")
L[-1] = L[-1].rstrip('\n')
for n in ns:
    L.append(f"  · subst h; exact col1_forced_{n} a hd")
L.append("""
theorem drv_of_periodic (T t0 : Nat) (hper : ∀ t, T ≤ t → center (t + 8) = center t) (ht0 : T ≤ t0)
    (hw : ∀ i, i < 6 → center (t0 + i) = false) (hb1 : center (t0 + 6) = true)
    (hb2 : center (t0 + 7) = true) : ∀ m t, cell (t0 + 8 * m + t) 0 = drv t := by
  intro m t
  have hp := periodic_mul hper (m + t / 8) (t0 + t % 8) (by omega)
  have hdm := Nat.div_add_mod t 8
  have e : t0 + t % 8 + (m + t / 8) * 8 = t0 + 8 * m + t := by
    rw [Nat.add_mul]; omega
  rw [e] at hp
  show center (t0 + 8 * m + t) = drv t
  rw [hp]
  have hlt := Nat.mod_lt t (show 0 < 8 by decide)
  unfold drv
  by_cases h6 : t % 8 < 6
  · rw [hw (t % 8) h6]
    exact (decide_eq_false (by omega)).symm
  · by_cases h7 : t % 8 = 6
    · rw [h7, hb1]; rfl
    · have : t % 8 = 7 := by omega
      rw [this, show t0 + 7 = t0 + 7 from rfl, hb2]; rfl

/-- **The word `0^6 1 1` is excluded**: the center column of rule 30 is not eventually periodic with
repeating word `0^6 1 1` (any phase), whatever the transient. -/
theorem no_white_run_6 (T t0 : Nat) (hper : ∀ t, T ≤ t → center (t + 8) = center t) (ht0 : T ≤ t0)
    (hw : ∀ i, i < 6 → center (t0 + i) = false) (hb1 : center (t0 + 6) = true)
    (hb2 : center (t0 + 7) = true) : False := by
  have hd := drv_of_periodic T t0 hper ht0 hw hb1 hb2
  have h1 : EventuallyPeriodic (fun t => cell t (0 + 1)) := by
    refine ⟨t0 + 33, 16, by decide, fun t ht => ?_⟩
    show cell (t + 16) (0 + 1) = cell t (0 + 1)
    rw [show (0 : Int) + 1 = 1 by rfl]
    have hdm := Nat.div_add_mod (t - t0 - 33) 8
    have hlt := Nat.mod_lt (t - t0 - 33) (show 0 < 8 by decide)
    have := col1_forced (t0 + 8 * ((t - t0 - 33) / 8)) (33 + (t - t0 - 33) % 8)
      (fun s => hd ((t - t0 - 33) / 8) s) (by omega) (by omega)
    rw [show t0 + 8 * ((t - t0 - 33) / 8) + (33 + (t - t0 - 33) % 8) = t by omega] at this
    exact this.symm
  have h0 : EventuallyPeriodic (fun t => cell t 0) := ⟨T, 8, by decide, hper⟩
  exact not_adjacent 0 h0 h1

end R30W6

#print axioms R30W6.no_white_run_6
#check @R30W6.no_white_run_6
""")
open(out, 'w').write('\n'.join(L) + '\n')
