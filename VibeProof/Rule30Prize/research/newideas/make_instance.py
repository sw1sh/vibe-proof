import sys
name, w, b = sys.argv[1], sys.argv[2], int(sys.argv[3])
core = open('lean/StripCertCore.lean').read()
data = open(f'lean/Cert_{name}.lean').read()
P = len(w)
inst = f"""
namespace R30NewIdeas
open Ruliology.CellularAutomata.Rule30Jen

{data}
def C_{name} : Cert := {{ w := {name}_w, b := {name}_b, nranks := {name}_nranks, rankP := {name}_rankP, posP := {name}_posP, perP := {name}_perP, wordP := {name}_wordP }}

theorem C_{name}_check : C_{name}.check = true := by decide +kernel
theorem C_{name}_checkG : C_{name}.checkG = true := by decide +kernel

/-- The center column of rule 30 is not eventually periodic with repeating block `{w}` (any phase: the
block starts at the time `T`). -/
theorem not_eventually_{name} (T : Nat)
    (h : ∀ t, T ≤ t → cell t 0 = C_{name}.wAt ((t - T) % C_{name}.P)) : False :=
  Cert.sound C_{name} C_{name}_check C_{name}_checkG (by decide) (by decide) T h

end R30NewIdeas
"""
open(f'lean/Inst_{name}.lean', 'w').write(core + inst + f"\n#print axioms R30NewIdeas.not_eventually_{name}\n")
