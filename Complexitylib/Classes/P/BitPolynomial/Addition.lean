/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Classes.P.Defs
public import Complexitylib.Encoding.BitPolynomial.Addition
public import Complexitylib.Tactic.PolyTime.Init
import Complexitylib.Classes.P.BitPolynomial.Addition.Internal

/-!
# Uniform polynomial-time binary-polynomial addition

The registered evaluator XORs two runtime coefficient lists with high zero
padding. Later polynomial programs can compose this certificate directly.
-/

public section

namespace Complexity
namespace BitPolynomial

/-- Padded addition of two runtime coefficient lists is uniformly polynomial-time. -/
@[polytime] theorem addEval_mem_FP : addEval ∈ FP := Internal.addEval_mem_FP

end BitPolynomial
end Complexity
