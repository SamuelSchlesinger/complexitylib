/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Classes.P.Defs
public import Complexitylib.Encoding.BitPolynomial.BlockEval
public import Complexitylib.Tactic.PolyTime.Init
import Complexitylib.Classes.P.BitPolynomial.BlockEval.Internal

/-!
# Uniform polynomial-time evaluation of coefficient blocks

A single evaluator reads a flat coefficient string, block-width word, seed,
modulus, and count word through nested pairing. Horner's rule processes the
requested blocks from high degree to low degree using bounded remainder
states. Missing coefficients are zero; malformed encodings follow the total
projections and zero moduli produce empty output.
-/

public section

namespace Complexity
namespace BitPolynomial

/-- Horner evaluation of runtime coefficient blocks is uniformly polynomial-time. -/
@[polytime] theorem blockEval_mem_FP : blockEval ∈ FP := Internal.blockEval_mem_FP

end BitPolynomial
end Complexity
