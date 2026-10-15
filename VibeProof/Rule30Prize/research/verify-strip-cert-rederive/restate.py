# Append an explicit, self-contained restatement (any transient, any rotation) to a copy of each instance file.
import sys, re
words = {"c01111111": "01111111", "c00000011": "00000011", "c0x10_1": "00000000001",
         "c000000000101": "000000000101", "c0011111111": "0011111111"}
for name, w in words.items():
    src = open(f"../newideas/lean/Inst_{name}.lean").read()
    P = len(w)
    lit = "[" + ", ".join("true" if ch == "1" else "false" for ch in w) + "]"
    # sanity: the file's word literal must equal ours
    m = re.search(rf"def {name}_w : List Bool := (\[[^\]]*\])", src)
    assert m and m.group(1) == lit, (name, m.group(1) if m else None, lit)
    extra = f"""

namespace VerifyRestate
open Ruliology.CellularAutomata.Rule30Jen

theorem no_tail_{name} :
    ¬ ∃ T : Nat, ∀ t, T ≤ t → cell t 0 = ({lit} : List Bool).getD ((t - T) % {P}) false :=
  fun ⟨T, h⟩ => R30NewIdeas.not_eventually_{name} T h

theorem no_tail_rot_{name} :
    ¬ ∃ T k : Nat, ∀ t, T ≤ t → cell t 0 = ({lit} : List Bool).getD ((t + k) % {P}) false := by
  rintro ⟨T, k, h⟩
  refine R30NewIdeas.not_eventually_{name} ({P} * T + ({P} - k % {P})) fun t ht => ?_
  rw [h t (by omega)]
  show _ = List.getD ({lit} : List Bool) ((t - ({P} * T + ({P} - k % {P}))) % {P}) false
  congr 1
  omega

end VerifyRestate

#print axioms VerifyRestate.no_tail_{name}
#print axioms VerifyRestate.no_tail_rot_{name}
"""
    open(f"Restate_{name}.lean", "w").write(src + extra)
    print("wrote", name, P, lit)
