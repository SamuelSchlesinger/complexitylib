/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Encoding.BitPolynomial.Addition.Defs
import Complexitylib.Encoding.BitPolynomial.Addition.Internal

/-!
# Correct padded binary-polynomial addition

The concrete coefficientwise XOR represents addition over `ZMod 2` for all
input lists, including empty operands and high zero padding. Its exact
length is the larger operand length. A uniform polynomial-time certificate
is supplied by `Complexitylib.Classes.P.BitPolynomial.Addition`.
-/

public section

namespace Complexity
namespace BitPolynomial

/-- Addition retains the larger operand width, including high zero padding. -/
theorem addBits_length (a b : List Bool) :
    (addBits a b).length = max a.length b.length :=
  Internal.addBits_length a b

/-- Padded coefficientwise XOR denotes polynomial addition. -/
theorem ofBits_addBits (a b : List Bool) : ofBits (addBits a b) = ofBits a + ofBits b :=
  Internal.ofBits_addBits a b

/-- The paired evaluator reads exactly its two operands. -/
theorem addEval_pair (a b : List Bool) : addEval (pair a b) = addBits a b := by
  simp only [addEval, pairFst_pair, pairSnd_pair]

end BitPolynomial
end Complexity
