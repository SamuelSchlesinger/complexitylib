/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Encoding.BitPolynomial.Defs
import Complexitylib.Encoding.BitPolynomial.Internal

/-!
# Correct carryless multiplication of binary polynomials

`BitPolynomial.ofBits` interprets a bit list as coefficients over `ZMod 2`,
constant coefficient first. `ofBits_mulBits` proves that the concrete parity
convolution computes polynomial multiplication for every pair of lists,
including empty lists and lists with high zero padding.

The result has length equal to the sum of the input lengths. For nonempty
operands its last coefficient is therefore zero. No normalization or
irreducibility assumption is needed. The uniform polynomial-time certificate
is in `Complexitylib.Classes.P.BitPolynomial`.
-/

public section

namespace Complexity
namespace BitPolynomial

/-- A represented polynomial's coefficient is the corresponding bit, or zero past the list. -/
theorem ofBits_coeff (bits : List Bool) (k : Nat) :
    (ofBits bits).coeff k = ((bits[k]?.getD false).toNat : ZMod 2) :=
  Internal.ofBits_coeff bits k

/-- Carryless multiplication retains exactly the sum of the two input lengths. -/
theorem mulBits_length (a b : List Bool) :
    (mulBits a b).length = a.length + b.length :=
  Internal.mulBits_length a b

/-- The concrete bit-list product denotes the product over the two-element field. -/
theorem ofBits_mulBits (a b : List Bool) :
    ofBits (mulBits a b) = ofBits a * ofBits b :=
  Internal.ofBits_mulBits a b

/-- On a paired input, the evaluator returns the carryless product of its two operands. -/
theorem mulEval_pair (a b : List Bool) : mulEval (pair a b) = mulBits a b := by
  simp only [mulEval, pairFst_pair, pairSnd_pair]

end BitPolynomial
end Complexity
