import D4_00
import D4_01
import D4_02
import D4_03
import D4_04
import D4_05
import D4_06
import D4_07
import D4_08
import D4_09
import D4_10
import D4_11
import D4_12
import D4_13
import D4_14
import W_00
import W_01
import W_02
import W_03
import W_04
import W_05
import W_06
import W_07
import W_08
import W_09
import W_10
import W_11
import W_12
import W_13
import W_14
import W_15
import W_16
import W_17
import W_18
import W_19
import W_20
import W_21
import W_22
import W_23
import W_24
import W_25
import W_26
import W_27
import W_28
import W_29
import W_30
import W_31
import W_32
import W_33
import W_34
import W_35
open Ruliology.CellularAutomata.Rule30Jen
open AbsorbRight

theorem allLists_0_eq : allLists 0 =
  [[]] := by decide +kernel

theorem det4_len0 : ∀ v ∈ allLists 0, Determined v 4 = true := by
  rw [allLists_0_eq]
  simp only [List.forall_mem_cons, List.not_mem_nil, false_imp_iff, imp_true_iff, and_true]
  exact W_wnil

theorem allLists_1_eq : allLists 1 =
  [[false],
   [true]] := by decide +kernel

theorem det4_len1 : ∀ v ∈ allLists 1, Determined v 4 = true := by
  rw [allLists_1_eq]
  simp only [List.forall_mem_cons, List.not_mem_nil, false_imp_iff, imp_true_iff, and_true]
  exact ⟨D4_b0, W_w1⟩

theorem allLists_2_eq : allLists 2 =
  [[false, false],
   [false, true],
   [true, false],
   [true, true]] := by decide +kernel

theorem det4_len2 : ∀ v ∈ allLists 2, Determined v 4 = true := by
  rw [allLists_2_eq]
  simp only [List.forall_mem_cons, List.not_mem_nil, false_imp_iff, imp_true_iff, and_true]
  exact ⟨D4_b00, W_w01, W_w10, W_w11⟩

theorem allLists_3_eq : allLists 3 =
  [[false, false, false],
   [false, false, true],
   [false, true, false],
   [false, true, true],
   [true, false, false],
   [true, false, true],
   [true, true, false],
   [true, true, true]] := by decide +kernel

theorem det4_len3 : ∀ v ∈ allLists 3, Determined v 4 = true := by
  rw [allLists_3_eq]
  simp only [List.forall_mem_cons, List.not_mem_nil, false_imp_iff, imp_true_iff, and_true]
  exact ⟨D4_b000, W_w001, D4_b010, W_w011, W_w100, W_w101, W_w110, W_w111⟩

theorem allLists_4_eq : allLists 4 =
  [[false, false, false, false],
   [false, false, false, true],
   [false, false, true, false],
   [false, false, true, true],
   [false, true, false, false],
   [false, true, false, true],
   [false, true, true, false],
   [false, true, true, true],
   [true, false, false, false],
   [true, false, false, true],
   [true, false, true, false],
   [true, false, true, true],
   [true, true, false, false],
   [true, true, false, true],
   [true, true, true, false],
   [true, true, true, true]] := by decide +kernel

theorem det4_len4 : ∀ v ∈ allLists 4, Determined v 4 = true := by
  rw [allLists_4_eq]
  simp only [List.forall_mem_cons, List.not_mem_nil, false_imp_iff, imp_true_iff, and_true]
  exact ⟨D4_b0000, W_w0001, D4_b0010, W_w0011, D4_b0100, W_w0101, D4_b0110, W_w0111, W_w1000, W_w1001, W_w1010, W_w1011, W_w1100, W_w1101, W_w1110, W_w1111⟩

theorem allLists_5_eq : allLists 5 =
  [[false, false, false, false, false],
   [false, false, false, false, true],
   [false, false, false, true, false],
   [false, false, false, true, true],
   [false, false, true, false, false],
   [false, false, true, false, true],
   [false, false, true, true, false],
   [false, false, true, true, true],
   [false, true, false, false, false],
   [false, true, false, false, true],
   [false, true, false, true, false],
   [false, true, false, true, true],
   [false, true, true, false, false],
   [false, true, true, false, true],
   [false, true, true, true, false],
   [false, true, true, true, true],
   [true, false, false, false, false],
   [true, false, false, false, true],
   [true, false, false, true, false],
   [true, false, false, true, true],
   [true, false, true, false, false],
   [true, false, true, false, true],
   [true, false, true, true, false],
   [true, false, true, true, true],
   [true, true, false, false, false],
   [true, true, false, false, true],
   [true, true, false, true, false],
   [true, true, false, true, true],
   [true, true, true, false, false],
   [true, true, true, false, true],
   [true, true, true, true, false],
   [true, true, true, true, true]] := by decide +kernel

theorem det4_len5 : ∀ v ∈ allLists 5, Determined v 4 = true := by
  rw [allLists_5_eq]
  simp only [List.forall_mem_cons, List.not_mem_nil, false_imp_iff, imp_true_iff, and_true]
  exact ⟨D4_b00000, W_w00001, D4_b00010, W_w00011, D4_b00100, W_w00101, D4_b00110, W_w00111, D4_b01000, W_w01001, D4_b01010, W_w01011, D4_b01100, W_w01101, D4_b01110, W_w01111, W_w10000, W_w10001, W_w10010, W_w10011, W_w10100, W_w10101, W_w10110, W_w10111, W_w11000, W_w11001, W_w11010, W_w11011, W_w11100, W_w11101, W_w11110, W_w11111⟩

theorem allLists_6_eq : allLists 6 =
  [[false, false, false, false, false, false],
   [false, false, false, false, false, true],
   [false, false, false, false, true, false],
   [false, false, false, false, true, true],
   [false, false, false, true, false, false],
   [false, false, false, true, false, true],
   [false, false, false, true, true, false],
   [false, false, false, true, true, true],
   [false, false, true, false, false, false],
   [false, false, true, false, false, true],
   [false, false, true, false, true, false],
   [false, false, true, false, true, true],
   [false, false, true, true, false, false],
   [false, false, true, true, false, true],
   [false, false, true, true, true, false],
   [false, false, true, true, true, true],
   [false, true, false, false, false, false],
   [false, true, false, false, false, true],
   [false, true, false, false, true, false],
   [false, true, false, false, true, true],
   [false, true, false, true, false, false],
   [false, true, false, true, false, true],
   [false, true, false, true, true, false],
   [false, true, false, true, true, true],
   [false, true, true, false, false, false],
   [false, true, true, false, false, true],
   [false, true, true, false, true, false],
   [false, true, true, false, true, true],
   [false, true, true, true, false, false],
   [false, true, true, true, false, true],
   [false, true, true, true, true, false],
   [false, true, true, true, true, true],
   [true, false, false, false, false, false],
   [true, false, false, false, false, true],
   [true, false, false, false, true, false],
   [true, false, false, false, true, true],
   [true, false, false, true, false, false],
   [true, false, false, true, false, true],
   [true, false, false, true, true, false],
   [true, false, false, true, true, true],
   [true, false, true, false, false, false],
   [true, false, true, false, false, true],
   [true, false, true, false, true, false],
   [true, false, true, false, true, true],
   [true, false, true, true, false, false],
   [true, false, true, true, false, true],
   [true, false, true, true, true, false],
   [true, false, true, true, true, true],
   [true, true, false, false, false, false],
   [true, true, false, false, false, true],
   [true, true, false, false, true, false],
   [true, true, false, false, true, true],
   [true, true, false, true, false, false],
   [true, true, false, true, false, true],
   [true, true, false, true, true, false],
   [true, true, false, true, true, true],
   [true, true, true, false, false, false],
   [true, true, true, false, false, true],
   [true, true, true, false, true, false],
   [true, true, true, false, true, true],
   [true, true, true, true, false, false],
   [true, true, true, true, false, true],
   [true, true, true, true, true, false],
   [true, true, true, true, true, true]] := by decide +kernel

theorem det4_len6 : ∀ v ∈ allLists 6, Determined v 4 = true := by
  rw [allLists_6_eq]
  simp only [List.forall_mem_cons, List.not_mem_nil, false_imp_iff, imp_true_iff, and_true]
  exact ⟨D4_b000000, W_w000001, D4_b000010, W_w000011, D4_b000100, W_w000101, D4_b000110, W_w000111, D4_b001000, W_w001001, D4_b001010, W_w001011, D4_b001100, W_w001101, D4_b001110, W_w001111, D4_b010000, W_w010001, D4_b010010, W_w010011, D4_b010100, W_w010101, D4_b010110, W_w010111, D4_b011000, W_w011001, D4_b011010, W_w011011, D4_b011100, W_w011101, D4_b011110, W_w011111, W_w100000, W_w100001, W_w100010, W_w100011, W_w100100, W_w100101, W_w100110, W_w100111, W_w101000, W_w101001, W_w101010, W_w101011, W_w101100, W_w101101, W_w101110, W_w101111, W_w110000, W_w110001, W_w110010, W_w110011, W_w110100, W_w110101, W_w110110, W_w110111, W_w111000, W_w111001, W_w111010, W_w111011, W_w111100, W_w111101, W_w111110, W_w111111⟩

theorem allLists_7_eq : allLists 7 =
  [[false, false, false, false, false, false, false],
   [false, false, false, false, false, false, true],
   [false, false, false, false, false, true, false],
   [false, false, false, false, false, true, true],
   [false, false, false, false, true, false, false],
   [false, false, false, false, true, false, true],
   [false, false, false, false, true, true, false],
   [false, false, false, false, true, true, true],
   [false, false, false, true, false, false, false],
   [false, false, false, true, false, false, true],
   [false, false, false, true, false, true, false],
   [false, false, false, true, false, true, true],
   [false, false, false, true, true, false, false],
   [false, false, false, true, true, false, true],
   [false, false, false, true, true, true, false],
   [false, false, false, true, true, true, true],
   [false, false, true, false, false, false, false],
   [false, false, true, false, false, false, true],
   [false, false, true, false, false, true, false],
   [false, false, true, false, false, true, true],
   [false, false, true, false, true, false, false],
   [false, false, true, false, true, false, true],
   [false, false, true, false, true, true, false],
   [false, false, true, false, true, true, true],
   [false, false, true, true, false, false, false],
   [false, false, true, true, false, false, true],
   [false, false, true, true, false, true, false],
   [false, false, true, true, false, true, true],
   [false, false, true, true, true, false, false],
   [false, false, true, true, true, false, true],
   [false, false, true, true, true, true, false],
   [false, false, true, true, true, true, true],
   [false, true, false, false, false, false, false],
   [false, true, false, false, false, false, true],
   [false, true, false, false, false, true, false],
   [false, true, false, false, false, true, true],
   [false, true, false, false, true, false, false],
   [false, true, false, false, true, false, true],
   [false, true, false, false, true, true, false],
   [false, true, false, false, true, true, true],
   [false, true, false, true, false, false, false],
   [false, true, false, true, false, false, true],
   [false, true, false, true, false, true, false],
   [false, true, false, true, false, true, true],
   [false, true, false, true, true, false, false],
   [false, true, false, true, true, false, true],
   [false, true, false, true, true, true, false],
   [false, true, false, true, true, true, true],
   [false, true, true, false, false, false, false],
   [false, true, true, false, false, false, true],
   [false, true, true, false, false, true, false],
   [false, true, true, false, false, true, true],
   [false, true, true, false, true, false, false],
   [false, true, true, false, true, false, true],
   [false, true, true, false, true, true, false],
   [false, true, true, false, true, true, true],
   [false, true, true, true, false, false, false],
   [false, true, true, true, false, false, true],
   [false, true, true, true, false, true, false],
   [false, true, true, true, false, true, true],
   [false, true, true, true, true, false, false],
   [false, true, true, true, true, false, true],
   [false, true, true, true, true, true, false],
   [false, true, true, true, true, true, true],
   [true, false, false, false, false, false, false],
   [true, false, false, false, false, false, true],
   [true, false, false, false, false, true, false],
   [true, false, false, false, false, true, true],
   [true, false, false, false, true, false, false],
   [true, false, false, false, true, false, true],
   [true, false, false, false, true, true, false],
   [true, false, false, false, true, true, true],
   [true, false, false, true, false, false, false],
   [true, false, false, true, false, false, true],
   [true, false, false, true, false, true, false],
   [true, false, false, true, false, true, true],
   [true, false, false, true, true, false, false],
   [true, false, false, true, true, false, true],
   [true, false, false, true, true, true, false],
   [true, false, false, true, true, true, true],
   [true, false, true, false, false, false, false],
   [true, false, true, false, false, false, true],
   [true, false, true, false, false, true, false],
   [true, false, true, false, false, true, true],
   [true, false, true, false, true, false, false],
   [true, false, true, false, true, false, true],
   [true, false, true, false, true, true, false],
   [true, false, true, false, true, true, true],
   [true, false, true, true, false, false, false],
   [true, false, true, true, false, false, true],
   [true, false, true, true, false, true, false],
   [true, false, true, true, false, true, true],
   [true, false, true, true, true, false, false],
   [true, false, true, true, true, false, true],
   [true, false, true, true, true, true, false],
   [true, false, true, true, true, true, true],
   [true, true, false, false, false, false, false],
   [true, true, false, false, false, false, true],
   [true, true, false, false, false, true, false],
   [true, true, false, false, false, true, true],
   [true, true, false, false, true, false, false],
   [true, true, false, false, true, false, true],
   [true, true, false, false, true, true, false],
   [true, true, false, false, true, true, true],
   [true, true, false, true, false, false, false],
   [true, true, false, true, false, false, true],
   [true, true, false, true, false, true, false],
   [true, true, false, true, false, true, true],
   [true, true, false, true, true, false, false],
   [true, true, false, true, true, false, true],
   [true, true, false, true, true, true, false],
   [true, true, false, true, true, true, true],
   [true, true, true, false, false, false, false],
   [true, true, true, false, false, false, true],
   [true, true, true, false, false, true, false],
   [true, true, true, false, false, true, true],
   [true, true, true, false, true, false, false],
   [true, true, true, false, true, false, true],
   [true, true, true, false, true, true, false],
   [true, true, true, false, true, true, true],
   [true, true, true, true, false, false, false],
   [true, true, true, true, false, false, true],
   [true, true, true, true, false, true, false],
   [true, true, true, true, false, true, true],
   [true, true, true, true, true, false, false],
   [true, true, true, true, true, false, true],
   [true, true, true, true, true, true, false],
   [true, true, true, true, true, true, true]] := by decide +kernel

theorem det4_len7 : ∀ v ∈ allLists 7, Determined v 4 = true := by
  rw [allLists_7_eq]
  simp only [List.forall_mem_cons, List.not_mem_nil, false_imp_iff, imp_true_iff, and_true]
  exact ⟨D4_b0000000, W_w0000001, D4_b0000010, W_w0000011, D4_b0000100, W_w0000101, D4_b0000110, W_w0000111, D4_b0001000, W_w0001001, D4_b0001010, W_w0001011, D4_b0001100, W_w0001101, D4_b0001110, W_w0001111, D4_b0010000, W_w0010001, D4_b0010010, W_w0010011, D4_b0010100, W_w0010101, D4_b0010110, W_w0010111, D4_b0011000, W_w0011001, D4_b0011010, W_w0011011, D4_b0011100, W_w0011101, D4_b0011110, W_w0011111, D4_b0100000, W_w0100001, D4_b0100010, W_w0100011, D4_b0100100, W_w0100101, D4_b0100110, W_w0100111, D4_b0101000, W_w0101001, D4_b0101010, W_w0101011, D4_b0101100, W_w0101101, D4_b0101110, W_w0101111, D4_b0110000, W_w0110001, D4_b0110010, W_w0110011, D4_b0110100, W_w0110101, D4_b0110110, W_w0110111, D4_b0111000, W_w0111001, D4_b0111010, W_w0111011, D4_b0111100, W_w0111101, D4_b0111110, W_w0111111, W_w1000000, W_w1000001, W_w1000010, W_w1000011, W_w1000100, W_w1000101, W_w1000110, W_w1000111, W_w1001000, W_w1001001, W_w1001010, W_w1001011, W_w1001100, W_w1001101, W_w1001110, W_w1001111, W_w1010000, W_w1010001, W_w1010010, W_w1010011, W_w1010100, W_w1010101, W_w1010110, W_w1010111, W_w1011000, W_w1011001, W_w1011010, W_w1011011, W_w1011100, W_w1011101, W_w1011110, W_w1011111, W_w1100000, W_w1100001, W_w1100010, W_w1100011, W_w1100100, W_w1100101, W_w1100110, W_w1100111, W_w1101000, W_w1101001, W_w1101010, W_w1101011, W_w1101100, W_w1101101, W_w1101110, W_w1101111, W_w1110000, W_w1110001, W_w1110010, W_w1110011, W_w1110100, W_w1110101, W_w1110110, W_w1110111, W_w1111000, W_w1111001, W_w1111010, W_w1111011, W_w1111100, W_w1111101, W_w1111110, W_w1111111⟩

open Ruliology.CellularAutomata.Rule30Prize

/-- `Determined v 4` for every word of length at most 7. -/
theorem det4_upto7 (v : List Bool) (hv : v.length ≤ 7) : Determined v 4 = true := by
  have hm := mem_allLists v
  have hcase : v.length = 0 ∨ v.length = 1 ∨ v.length = 2 ∨ v.length = 3 ∨ v.length = 4 ∨
      v.length = 5 ∨ v.length = 6 ∨ v.length = 7 := by omega
  rcases hcase with h | h | h | h | h | h | h | h <;> rw [h] at hm
  · exact det4_len0 v hm
  · exact det4_len1 v hm
  · exact det4_len2 v hm
  · exact det4_len3 v hm
  · exact det4_len4 v hm
  · exact det4_len5 v hm
  · exact det4_len6 v hm
  · exact det4_len7 v hm

theorem getD_map_range (f : Nat → Bool) : ∀ (n i : Nat), i < n →
    ((List.range n).map f).getD i false = f i := by
  intro n i h
  simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range h]

/-- **Corollary (formal "Hence").** If the center column has period `P` from `T` on, no window
`[t1, t1 + r)` with `t1 ≥ T` is all black when `r ≥ 36` and `P ≤ r + 7`: no repeating word consists
of a black run of length at least 36 plus at most 7 other symbols. -/
theorem no_black_run_plus_seven (T P t1 r : Nat) (hr : 36 ≤ r) (hrP : r ≤ P) (hP7 : P ≤ r + 7)
    (hper : ∀ t, T ≤ t → center (t + P) = center t) (ht1 : T ≤ t1)
    (hrun : ∀ s, s < r → center (t1 + s) = true) : False := by
  let v : List Bool := (List.range (P - r)).map fun i => center (t1 + r + i)
  have hlen : v.length = P - r := by simp [v]
  have hper' : ∀ t, T ≤ t → center (t + (r + v.length)) = center t := by
    intro t ht
    rw [hlen, show r + (P - r) = P by omega]
    exact hper t ht
  exact no_black_run_block v 4 (det4_upto7 v (by omega)) (by omega) T r t1 hper' ht1
    (by omega) (by omega) hrun (fun i hi => by
      rw [hlen] at hi
      exact (getD_map_range (fun i => center (t1 + r + i)) (P - r) i hi).symm)

#print axioms det4_upto7
#print axioms no_black_run_plus_seven
