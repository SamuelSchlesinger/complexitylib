/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Encoding.BitPolynomial.Remainder.Defs
public import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
import Complexitylib.Encoding.BitPolynomial
import Mathlib.Tactic.Linarith

/-!
# Significant lengths of binary coefficient lists

The bounded maximum defining significant length identifies zero polynomials
and the degree and monicity of every nonzero represented polynomial.
-/

public section

namespace Complexity
namespace BitPolynomial.Internal

theorem significantLength_le (bits : List Bool) : significantLength bits ≤ bits.length := by
  apply Finset.sup_le
  intro i hi
  have := Finset.mem_range.mp hi
  split <;> lia

theorem bit_eq_false_of_significantLength_le (bits : List Bool) (i : Nat)
    (hi : significantLength bits ≤ i) : bits[i]?.getD false = false := by
  by_cases hb : i < bits.length
  · have h := Finset.le_sup (f := fun j => if bits[j]?.getD false then j + 1 else 0)
      (Finset.mem_range.mpr hb)
    change (if bits[i]?.getD false then i + 1 else 0) ≤ significantLength bits at h
    cases hv : bits[i]?.getD false
    · rfl
    · simp only [hv, ite_true] at h
      lia
  · simp [List.getElem?_eq_none (Nat.le_of_not_gt hb)]

theorem bit_at_significantLength (bits : List Bool) (h : 0 < significantLength bits) :
    bits[significantLength bits - 1]?.getD false = true := by
  have hlen : 0 < bits.length := lt_of_lt_of_le h (significantLength_le bits)
  obtain ⟨i, _, heq⟩ := Finset.exists_mem_eq_sup (Finset.range bits.length)
    ⟨0, Finset.mem_range.mpr hlen⟩
    (fun j => if bits[j]?.getD false then j + 1 else 0)
  change significantLength bits = (if bits[i]?.getD false then i + 1 else 0) at heq
  cases hv : bits[i]?.getD false
  · simp only [hv, Bool.false_eq_true, ite_false] at heq
    lia
  · simp only [hv, ite_true] at heq
    simpa only [heq, Nat.add_sub_cancel] using hv

theorem significantLength_eq_zero_iff (bits : List Bool) :
    significantLength bits = 0 ↔ ofBits bits = 0 := by
  constructor
  · intro h
    ext i
    rw [BitPolynomial.ofBits_coeff, Polynomial.coeff_zero,
      bit_eq_false_of_significantLength_le bits i (by lia)]
    rfl
  · intro h
    by_contra hn
    have ht := bit_at_significantLength bits (Nat.pos_of_ne_zero hn)
    have hc := congr_arg (fun p : Polynomial (ZMod 2) => p.coeff (significantLength bits - 1)) h
    rw [BitPolynomial.ofBits_coeff, ht] at hc
    norm_num at hc

theorem ofBits_isMonicOfDegree (bits : List Bool) (h : 0 < significantLength bits) :
    (ofBits bits).IsMonicOfDegree (significantLength bits - 1) := by
  apply (Polynomial.isMonicOfDegree_iff _ _).mpr
  constructor
  · apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    intro i hi
    rw [BitPolynomial.ofBits_coeff,
      bit_eq_false_of_significantLength_le bits i (by lia)]
    rfl
  · rw [BitPolynomial.ofBits_coeff, bit_at_significantLength bits h]
    rfl

end BitPolynomial.Internal
end Complexity
