import Ruliology.CellularAutomata.Rule30StripCertificates
namespace Ruliology.CellularAutomata.Rule30StripCertificates

#check @Nat.mod_add_mod
#check @Nat.add_mul_mod_self_left

/-- White phases met by the counter in `n` steps from phase `φ`. -/
def Cert.whites (C : Cert) (φ : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => (if C.wAt φ then 0 else 1) + Cert.whites C ((φ + 1) % C.P) n

theorem Cert.iterG_formula (C : Cert) (r : Nat) (hm : 0 < C.m r) (hP : 0 < C.P) :
    ∀ n φ p, φ < C.P → p < C.m r →
      C.iterG r n (p, φ) = ((p + C.whites φ n) % C.m r, (φ + n) % C.P)
  | 0, φ, p, hφ, hp => by
    simp only [Cert.iterG, Cert.whites, Nat.add_zero, Nat.mod_eq_of_lt hp, Nat.mod_eq_of_lt hφ]
  | n + 1, φ, p, hφ, hp => by
    have hφ' : (φ + 1) % C.P < C.P := Nat.mod_lt _ hP
    have hp' : C.nextPos r p φ < C.m r := by
      unfold Cert.nextPos
      split
      · exact hp
      · exact Nat.mod_lt _ hm
    show C.iterG r n (C.G r (p, φ)) = _
    rw [show C.G r (p, φ) = (C.nextPos r p φ, (φ + 1) % C.P) from rfl,
      Cert.iterG_formula C r hm hP n _ _ hφ' hp', Nat.mod_add_mod,
      show φ + 1 + n = φ + (n + 1) by omega]
    congr 1
    show (C.nextPos r p φ + C.whites ((φ + 1) % C.P) n) % C.m r =
      (p + ((if C.wAt φ then 0 else 1) + C.whites ((φ + 1) % C.P) n)) % C.m r
    unfold Cert.nextPos
    cases C.wAt φ
    · simp only [Bool.false_eq_true, if_false]
      rw [Nat.mod_add_mod, Nat.add_assoc]
    · simp only [if_true, Nat.zero_add]

theorem Cert.iterG_mul (C : Cert) (r : Nat) (hm : 0 < C.m r) (hP : 0 < C.P) (φ : Nat)
    (hφ : φ < C.P) : ∀ k p, p < C.m r →
      C.iterG r (k * C.P) (p, φ) = ((p + k * C.whites φ C.P) % C.m r, φ)
  | 0, p, hp => by simp [Cert.iterG, Nat.mod_eq_of_lt hp]
  | k + 1, p, hp => by
    rw [show (k + 1) * C.P = C.P + k * C.P by rw [Nat.succ_mul]; omega, iterG_add,
      Cert.iterG_formula C r hm hP C.P φ p hφ hp, Nat.add_mod_right, Nat.mod_eq_of_lt hφ,
      Cert.iterG_mul C r hm hP φ hφ k _ (Nat.mod_lt _ hm), Nat.mod_add_mod]
    congr 2
    rw [Nat.succ_mul]
    omega

/-- **The counter-phase map has period `m · P`.** -/
theorem Cert.iterG_period (C : Cert) (r : Nat) (hm : 0 < C.m r) (hP : 0 < C.P) (p φ : Nat)
    (hp : p < C.m r) (hφ : φ < C.P) : C.iterG r (C.m r * C.P) (p, φ) = (p, φ) := by
  rw [Cert.iterG_mul C r hm hP φ hφ (C.m r) p hp, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hp]

end Ruliology.CellularAutomata.Rule30StripCertificates
