/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Encoding.BitPolynomial.Addition.Defs
import Complexitylib.Encoding.BitPolynomial

/-!
# Correctness of padded binary-polynomial addition

Each in-range XOR is addition in `ZMod 2`. Beyond the maximum operand length,
all three coefficient lists represent zero coefficients.
-/

public section

namespace Complexity
namespace BitPolynomial.Internal

theorem addBits_length (a b : List Bool) :
    (addBits a b).length = max a.length b.length := by
  simp only [addBits, List.length_map, List.length_range]

theorem ofBits_addBits (a b : List Bool) : ofBits (addBits a b) = ofBits a + ofBits b := by
  ext i
  rw [Polynomial.coeff_add, BitPolynomial.ofBits_coeff, BitPolynomial.ofBits_coeff,
    BitPolynomial.ofBits_coeff]
  by_cases bound : i < max a.length b.length
  · rw [addBits, List.getElem?_map, List.getElem?_range bound]
    simp only [Option.map_some, Option.getD_some]
    cases a[i]?.getD false <;> cases b[i]?.getD false <;> decide
  · have ha : a.length ≤ i := (le_max_left _ _).trans (Nat.le_of_not_gt bound)
    have hb : b.length ≤ i := (le_max_right _ _).trans (Nat.le_of_not_gt bound)
    have hout : (addBits a b).length ≤ i := by rw [addBits_length]; lia
    simp only [List.getElem?_eq_none ha, List.getElem?_eq_none hb,
      List.getElem?_eq_none hout, Option.getD_none, Bool.toNat_false, Nat.cast_zero, add_zero]

end BitPolynomial.Internal
end Complexity
