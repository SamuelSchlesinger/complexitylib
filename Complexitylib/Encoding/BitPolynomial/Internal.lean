/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Encoding.BitPolynomial.Defs
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Tactic.Linarith

/-!
# Correctness of carryless polynomial multiplication

The product coefficient is a convolution over the two coefficient lists.
Counting the true summands and reducing that count modulo two gives exactly
`mulBits`, including its high zero padding and empty input cases.
-/

public section

namespace Complexity
namespace BitPolynomial.Internal

open scoped BigOperators

theorem ofBits_coeff (bits : List Bool) (k : Nat) :
    (ofBits bits).coeff k = ((bits[k]?.getD false).toNat : ZMod 2) := by
  by_cases hk : k < bits.length
  · simp only [ofBits, Polynomial.ofFn_coeff_eq_val_of_lt _ hk,
      List.getElem?_eq_getElem hk, Option.getD_some, Fin.getElem_fin]
  · simp [ofBits, Polynomial.ofFn_coeff_eq_zero_of_ge _ (Nat.le_of_not_gt hk),
      List.getElem?_eq_none (Nat.le_of_not_gt hk)]

private theorem cast_parity (n : Nat) :
    ((decide (n % 2 = 1)).toNat : ZMod 2) = (n : ZMod 2) := by
  rw [← ZMod.natCast_mod n 2]
  by_cases h : n % 2 = 1
  · simp [h]
  · have hz : n % 2 = 0 := by have := Nat.mod_lt n (by decide : 0 < 2); lia
    simp [hz]

private theorem product_coeff (a b : List Bool) (k : Nat) :
    (ofBits a * ofBits b).coeff k =
      (((Finset.range a.length).filter fun i =>
        i ≤ k ∧ a[i]?.getD false = true ∧ b[k - i]?.getD false = true).card : ZMod 2) := by
  rw [Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => (ofBits a).coeff i * (ofBits b).coeff j) k]
  simp_rw [ofBits_coeff]
  have hsum :
      (∑ i ∈ Finset.range (k + 1),
        ((a[i]?.getD false).toNat : ZMod 2) * ((b[k - i]?.getD false).toNat : ZMod 2)) =
      ∑ i ∈ (Finset.range a.length).filter (fun i => i ≤ k),
        ((a[i]?.getD false).toNat : ZMod 2) * ((b[k - i]?.getD false).toNat : ZMod 2) := by
    symm
    refine Finset.sum_subset ?_ ?_
    · intro i hi
      simp only [Finset.mem_filter, Finset.mem_range] at hi ⊢
      lia
    · intro i hi hnot
      simp only [Finset.mem_range] at hi
      have ha : a.length ≤ i := by
        simp only [Finset.mem_filter, Finset.mem_range] at hnot
        lia
      simp [List.getElem?_eq_none ha]
  rw [hsum, Finset.sum_filter, ← Finset.sum_boole]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hik : i ≤ k
  · simp only [hik, ite_true, true_and]
    cases a[i]?.getD false <;> cases b[k - i]?.getD false <;> simp
  · simp [hik]

theorem mulBits_length (a b : List Bool) :
    (mulBits a b).length = a.length + b.length := by
  simp [mulBits]

theorem ofBits_mulBits (a b : List Bool) :
    ofBits (mulBits a b) = ofBits a * ofBits b := by
  ext k
  rw [ofBits_coeff, product_coeff]
  by_cases hk : k < a.length + b.length
  · rw [mulBits, List.getElem?_map, List.getElem?_range hk]
    exact cast_parity _
  · have hout : (mulBits a b)[k]? = none :=
      List.getElem?_eq_none (by rw [mulBits_length]; lia)
    rw [hout]
    have hempty : ((Finset.range a.length).filter fun i =>
        i ≤ k ∧ a[i]?.getD false = true ∧ b[k - i]?.getD false = true) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_range] at hi
      have hb : b.length ≤ k - i := by lia
      simpa [List.getElem?_eq_none hb] using hi.2.2.2
    simp [hempty]

end BitPolynomial.Internal
end Complexity
