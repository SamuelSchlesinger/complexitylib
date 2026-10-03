/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Encoding.BitPolynomial.Trinomial.Defs
import Complexitylib.Encoding.BitPolynomial
import Mathlib.Tactic.NormNum

/-!
# Correctness of the sparse trinomial coefficient generator

Each of the three distinguished positions lies inside the output list.
For a positive half-degree they are distinct; at zero, all three unit
coefficients sum to one in `ZMod 2`.
-/

public section

namespace Complexity
namespace BitPolynomial.Internal

theorem trinomialBits_length (d : Nat) : (trinomialBits d).length = 2 * d + 1 := by
  simp [trinomialBits]

private theorem trinomialBits_get (d i : Nat) :
    (trinomialBits d)[i]?.getD false = decide (i = 0 ∨ i = d ∨ i = 2 * d) := by
  by_cases hi : i < 2 * d + 1
  · simp [trinomialBits, List.getElem?_range hi]
  · have hout : (trinomialBits d)[i]? = none :=
      List.getElem?_eq_none (by rw [trinomialBits_length]; lia)
    have h0 : i ≠ 0 := by lia
    have hd : i ≠ d := by lia
    have h2d : i ≠ 2 * d := by lia
    simp [hout, h0, hd, h2d]

theorem ofBits_trinomialBits (d : Nat) :
    ofBits (trinomialBits d) =
      Polynomial.X ^ (2 * d) + Polynomial.X ^ d + 1 := by
  ext i
  rw [BitPolynomial.ofBits_coeff, trinomialBits_get]
  simp only [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_one]
  by_cases hd : d = 0
  · subst d
    by_cases hi : i = 0 <;> norm_num [hi, eq_comm]
    decide
  · have h2d : 2 * d ≠ 0 := by lia
    have distinct : d ≠ 2 * d := by lia
    by_cases h0 : i = 0
    · subst i
      norm_num [hd, h2d, Ne.symm hd]
    · by_cases hi : i = d
      · subst i
        norm_num [hd, distinct, Ne.symm distinct]
      · by_cases hlast : i = 2 * d
        · subst i
          norm_num [h2d, distinct, Ne.symm distinct]
        · norm_num [h0, hi, hlast, eq_comm]

end BitPolynomial.Internal
end Complexity
