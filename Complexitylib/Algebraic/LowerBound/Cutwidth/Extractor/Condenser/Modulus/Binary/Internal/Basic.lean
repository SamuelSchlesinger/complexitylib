/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Modulus.Binary.Defs
public import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Degree and the base quadratic of the binary modulus family

The leading exponent is strictly larger than the two remaining exponents.
At exponent zero, the quadratic has no root in the two-element field.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

theorem binaryModulus_monic (s : Nat) : (binaryModulus s).Monic := by
  have positive : 0 < 3 ^ s := by positivity
  have small : (Polynomial.X ^ (3 ^ s) + (1 : Polynomial (ZMod 2))).degree <
      ((2 * 3 ^ s : Nat) : WithBot Nat) := by
    rw [← Polynomial.C_1, Polynomial.degree_X_pow_add_C positive]
    exact_mod_cast (show 3 ^ s < 2 * 3 ^ s by lia)
  simpa only [binaryModulus, add_assoc] using Polynomial.monic_X_pow_add small

theorem binaryModulus_natDegree (s : Nat) : (binaryModulus s).natDegree = 2 * 3 ^ s := by
  have positive : 0 < 3 ^ s := by positivity
  rw [binaryModulus, add_assoc, Polynomial.natDegree_add_eq_left_of_natDegree_lt]
  · exact Polynomial.natDegree_X_pow _
  · rw [Polynomial.natDegree_X_pow, ← Polynomial.C_1, Polynomial.natDegree_X_pow_add_C]
    lia

theorem binaryModulus_zero_irreducible : Irreducible (binaryModulus 0) := by
  apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
  · simp [binaryModulus_natDegree]
  · intro x
    simp only [binaryModulus, pow_zero, mul_one, pow_one, Polynomial.IsRoot,
      Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one]
    fin_cases x <;> decide

end Algebraic.Cutwidth.Extractor.Internal
