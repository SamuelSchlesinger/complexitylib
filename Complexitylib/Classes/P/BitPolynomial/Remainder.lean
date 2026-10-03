/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Classes.P.Unary.Defs
public import Complexitylib.Encoding.BitPolynomial.Remainder
public import Complexitylib.Tactic.PolyTime.Init
import Complexitylib.Classes.P.BitPolynomial.Remainder.Internal

/-!
# Uniform polynomial-time remainder by binary polynomials

One deterministic polynomial-time evaluator computes the remainder of two
runtime coefficient lists, including padded and zero moduli. The proof uses
a bounded maximum to find the modulus width and a bounded high-to-low fold
for long division. The registered certificates support automatic composition
with later encoded polynomial and finite-field programs.
-/

public section

namespace Complexity
namespace BitPolynomial

/-- The significant coefficient width is computable in unary in polynomial time. -/
@[polytime] theorem significantLength_unary : UnaryFn significantLength :=
  Internal.significantLength_unary

/-- Remainder by a runtime binary modulus is uniformly polynomial-time. -/
@[polytime] theorem remainderEval_mem_FP : remainderEval ∈ FP :=
  Internal.remainderEval_mem_FP

end BitPolynomial
end Complexity
