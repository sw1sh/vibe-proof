import re
R = '/Users/swish/.claude/jobs/b8cd2926/tmp/r30prize/'
rz = open(R + 'complexity/lean/Rule30Realize.lean').read().split('\n')
br = open(R + 'complexity/lean/Rule30Barrier.lean').read().split('\n')
def L(lines, a, b):
    return '\n'.join(lines[a - 1:b])

header = r'''import Ruliology.CellularAutomata.Rule30Jen

/-!
# Rule 30: every column is realizable, and Jen's hypotheses do not decide Problem 1

Two barriers for proofs of Problem 1.

**Realization.** Run rule 30 from an arbitrary configuration `x : Int → Bool` (`evol x`).
* `realize`, `unique`, `column_realizable_unique`: **for every right half `R` (positions
  `p ≥ 1`) and every target column `c : Nat → Bool` there is exactly one configuration that
  agrees with `R` on `p ≥ 1` and whose column `0` is `c`.** The left half is rebuilt column by
  column by left-permutivity (`lc`); the right half is the half driven by `c` (`rh`).
* `seed_perturbation`: for every `n` some configuration agrees with the single seed on all
  positions `≥ -n`, has column `0` equal to the rule-30 center column up to time `n`, and white
  from then on. So no argument that ignores the far left of the configuration can show that the
  center column is not eventually constant, let alone aperiodic. (It necessarily differs from
  the seed at infinitely many positions `< -n`.)

**Rules 90, 150 and 210.** Consider `left xor g(center, right)` from a single black cell
(`run g`), for any `g` with `g 0 0 = 0` and `g 0 1 = 1`; rule 30 is `g = or` (`run30_eq_cell`).
* `run_not_adjacent`: every such rule is left-permutive with a left edge moving one cell per
  step, and Jen's adjacent-column theorem holds for it verbatim.
* `center90`, `center150`, `center210`, `barrier`: for `g = fun _ r => r` (rule 90),
  `g = xor` (rule 150) and `g = fun c r => !c && r` (rule 210, nonlinear and not right-permutive,
  like rule 30) the single-seed center column is eventually constant. So left-permutivity, the
  left edge and Jen's theorem cannot by themselves imply Problem 1, not even its period-1 case;
  a proof must use something specific to rule 30's `or` together with the finite seed.

Sources: the Rule 30 Prize project (2026), complexity and barrier analysis. Jen's argument is
E. Jen, *Global properties of cellular automata*, J. Stat. Phys. 43 (1986) 219–242.
-/

namespace Ruliology.CellularAutomata
namespace Rule30Realization

open Rule30Jen

/-! ### Realization from an arbitrary configuration -/
'''
out = [header]
out.append(L(rz, 19, 229))
out.append('')
out.append('/-! ### Left-permutive rules from a single seed -/')
out.append('')
b = L(br, 21, 208)
# rename the general Jen lemmas to avoid clashes with `Rule30Jen`
b = re.sub(r'\bperiodic_left_all\b', 'run_periodic_left_all', b)
b = re.sub(r'(?<!run_)\bperiodic_left\b', 'run_periodic_left', b)
b = re.sub(r'\bno_left_periodic\b', 'run_no_left_periodic', b)
b = re.sub(r'\bnot_adjacent\b', 'run_not_adjacent', b)
b = b.replace('Ruliology.CellularAutomata.Rule30Jen.cell t p', 'cell t p')
out.append(b)
out.append('')
out.append('end Rule30Realization')
out.append('end Ruliology.CellularAutomata')
open(R + 'staging/Ruliology/CellularAutomata/Rule30Realization.lean', 'w').write('\n'.join(out) + '\n')
print('written')
