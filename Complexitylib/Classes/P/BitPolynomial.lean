/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Classes.P.Defs
public import Complexitylib.Encoding.BitPolynomial
public import Complexitylib.Tactic.PolyTime.Init
import Complexitylib.Classes.P.BitPolynomial.Internal

/-!
# Carryless polynomial multiplication in polynomial time

The single evaluator `BitPolynomial.mulEval` reads both operand coefficient
lists from the standard pairing codec and computes their product over
`ZMod 2`. Its `FP` certificate uses the library's deterministic machine model
uniformly over all input lengths. The coefficient lists are runtime inputs;
there is no field modulus or hardwired polynomial in this construction.
On malformed pairings, the total projections give a possibly nonempty padding
of zero coefficients.
-/

public section

namespace Complexity
namespace BitPolynomial

/-- Carryless multiplication of two runtime coefficient lists is uniformly polynomial-time. -/
@[polytime] theorem mulEval_mem_FP : mulEval ∈ FP :=
  Internal.mulEval_mem_FP

end BitPolynomial
end Complexity
