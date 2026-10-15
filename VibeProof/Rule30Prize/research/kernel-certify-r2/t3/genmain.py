import os
ALIGN = {'0001': [(5, 0), (6, 0)], '0011': [(0, 0), (1, 3), (4, 0)], '0111': [(2, 2)]}
base = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'src', 'KC')
with open(os.path.join(base, 'EtherTrapMain.lean'), 'w') as f:
    for i in range(6): f.write(f'import KC.EtherTrapCerts{i}\n')
    f.write('''
/-!
# The pure-ether strip lies in no trap of width `≤ 20`

For each of the words `0001`, `0011`, `0111`, each ether alignment `(j₀, s)` of the word
(`Rule30Ether.A0001`, `A0011`, `A0111`), each phase `φ < 4` and each width `1 ≤ b ≤ 20`: every set of
strip nodes closed under every input that contains the pure-ether node
`(φ, etherRow j₀ ((φ + s) % 4) b)` contains a path whose column `1` at the white phases is not
eventually periodic (`pure_ether_escapes_*`). Hence no trap of width `≤ 20` contains the pure-ether
node (`pure_ether_not_in_trap_*`).
-/

namespace KC.EtherTrap
open Ruliology.CellularAutomata Rule30Ether Rule30StripCertificates

/-- From a width-`20` certificate to every width `1 ≤ b ≤ 20`. -/
theorem escape_of_cert20 (w : List Bool) (j0 s φ : Nat) (P A B : List Bool) (j0w : Nat)
    (hc : certOK w (φ, etherRow j0 ((φ + s) % 4) 20) P A B j0w = true)
    (b : Nat) (hb1 : 1 ≤ b) (hb : b ≤ 20) (T : Nat × List Bool → Prop) (hT : Closed w T)
    (hx : T (φ, etherRow j0 ((φ + s) % 4) b)) :
    ∃ u : Nat → Bool, (∀ n, T (traj w (φ, etherRow j0 ((φ + s) % 4) b) u n)) ∧
      ¬ MaskedPer w (traj w (φ, etherRow j0 ((φ + s) % 4) b) u) := by
  rcases Nat.lt_or_ge b 20 with h | h
  · obtain ⟨u, -, hu⟩ := escapes_of_certOK w _ P A B j0w hc (fun _ => True) (fun _ _ _ => trivial) trivial
    have e : etherRow j0 ((φ + s) % 4) b = (etherRow j0 ((φ + s) % 4) 20).take b := by
      unfold etherRow; rw [take_seg _ _ _ (by omega)]
    rw [e] at hx ⊢
    exact escapes_take w b hb1 (φ, etherRow j0 ((φ + s) % 4) 20)
      (by unfold etherRow; rw [length_seg]; exact h) u hu T hT hx
  · rw [show b = 20 by omega] at hx ⊢
    exact escapes_of_certOK w _ P A B j0w hc T hT hx

''')
    for w, al in ALIGN.items():
        f.write(f'''/-- **`{w}`: the pure ether escapes every closed set of width `≤ 20`.** -/
theorem pure_ether_escapes_{w} (a : Nat × Nat) (ha : a ∈ A{w}) (φ : Nat) (hφ : φ < 4) (b : Nat)
    (hb1 : 1 ≤ b) (hb : b ≤ 20) (T : Nat × List Bool → Prop) (hT : Closed w{w} T)
    (hx : T (φ, etherRow a.1 ((φ + a.2) % 4) b)) :
    ∃ u : Nat → Bool, (∀ n, T (traj w{w} (φ, etherRow a.1 ((φ + a.2) % 4) b) u n)) ∧
      ¬ MaskedPer w{w} (traj w{w} (φ, etherRow a.1 ((φ + a.2) % 4) b) u) := by
  simp only [A{w}, List.mem_cons, List.not_mem_nil, or_false] at ha
''')
        n = len(al)
        pat = ' | '.join(['rfl'] * n)
        f.write(f'  rcases ha with {pat} <;>\n    rcases (show φ = 0 ∨ φ = 1 ∨ φ = 2 ∨ φ = 3 by omega) with rfl | rfl | rfl | rfl\n')
        for (j0, s) in al:
            for ph in range(4):
                f.write(f'  · exact escape_of_cert20 w{w} {j0} {s} {ph} _ _ _ _ cert_{w}_{j0}_{ph} b hb1 hb T hT hx\n')
        f.write(f'''
/-- **`{w}`: no trap of width `≤ 20` contains a pure-ether node.** -/
theorem pure_ether_not_in_trap_{w} (a : Nat × Nat) (ha : a ∈ A{w}) (φ : Nat) (hφ : φ < 4) (b : Nat)
    (hb1 : 1 ≤ b) (hb : b ≤ 20) (T : Nat × List Bool → Prop) (hT : Trap w{w} T) :
    ¬ T (φ, etherRow a.1 ((φ + a.2) % 4) b) := by
  intro hx
  obtain ⟨u, -, hu⟩ := pure_ether_escapes_{w} a ha φ hφ b hb1 hb T hT.1 hx
  exact hu (hT.2 _ hx u)

''')
    f.write('end KC.EtherTrap\n')
