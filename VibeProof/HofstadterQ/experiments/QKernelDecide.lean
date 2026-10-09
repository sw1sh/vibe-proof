inductive Trie where
  | nil : Trie
  | node : Nat → Trie → Trie → Trie

/-- Bit-trie lookup (LSB-first path), fuel-bounded so it is structural. -/
def Trie.get : Nat → Trie → Nat → Nat
  | _, .nil, _ => 0
  | 0, .node v _ _, _ => v
  | f+1, .node v l r, k =>
    cond (Nat.beq k 0) v
      (cond (Nat.beq (k % 2) 0) (Trie.get f l (k / 2)) (Trie.get f r (k / 2)))

def Trie.set : Nat → Trie → Nat → Nat → Trie
  | 0, _, _, v => .node v .nil .nil
  | f+1, .nil, k, v =>
    cond (Nat.beq k 0) (.node v .nil .nil)
      (cond (Nat.beq (k % 2) 0) (.node 0 (Trie.set f .nil (k / 2) v) .nil)
        (.node 0 .nil (Trie.set f .nil (k / 2) v)))
  | f+1, .node w l r, k, v =>
    cond (Nat.beq k 0) (.node v l r)
      (cond (Nat.beq (k % 2) 0) (.node w (Trie.set f l (k / 2) v) r)
        (.node w l (Trie.set f r (k / 2) v)))

def qLoop : Nat → Nat → Trie → Bool
  | 0, _, _ => true
  | s+1, n, t =>
    let x := t.get 40 (n - 1)
    let y := t.get 40 (n - 2)
    cond (Nat.ble n x || Nat.ble n y) false
      (qLoop s (n + 1) (t.set 40 n (t.get 40 (n - x) + t.get 40 (n - y))))

def qInit : Trie := (Trie.nil.set 40 1 1).set 40 2 1
def qDefinedUpToK (N : Nat) : Bool := qLoop (N - 2) 3 qInit

#eval qDefinedUpToK 1000
theorem k_N : qDefinedUpToK 1000 = true := by decide +kernel
