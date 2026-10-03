/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Classes.P.Defs
public import Complexitylib.Encoding.BitPolynomial.Frobenius
public import Complexitylib.Tactic.PolyTime.Init
import Complexitylib.Classes.P.BitPolynomial.Frobenius.Internal

/-!
# Uniform polynomial-time binary modular Frobenius

The single evaluator takes a dividend, modulus, and count through nested
pairing. It performs one guarded modular square per count bit using runtime
multiplication and remainder. Every state is bounded by the modulus length;
a zero modulus gives the empty output. The registered certificate supports
composition in subsequent finite-field and condenser programs.
-/

public section

namespace Complexity
namespace BitPolynomial

/-- Bounded modular Frobenius with three runtime inputs is uniformly polynomial-time. -/
@[polytime] theorem frobeniusEval_mem_FP : frobeniusEval ∈ FP :=
  Internal.frobeniusEval_mem_FP

end BitPolynomial
end Complexity
