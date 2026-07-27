/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Classes.PPoly.Uniform.Containment.Internal

/-!
# Uniform polynomial-size circuits are in P

The uniformity generator is first promoted from logarithmic space to
polynomial time. A generic fanout combinator then constructs the serialized
`pair code input` expected by the verified quadratic circuit evaluator.

## Main results

- `circuitEvalLanguage_mem_P` — serialized circuit evaluation is in `P`
- `UniformPPoly_subset_P` — logspace-uniform polynomial-size circuits are in `P`
-/

@[expose] public section

namespace Complexity

/-- The language recognized by the verified serialized circuit-family
evaluator belongs to `P`. -/
theorem circuitEvalLanguage_mem_P : CircuitCode.circuitEvalLanguage ∈ P :=
  circuitEvalLanguage_mem_P_internal

/-- **Logspace-uniform polynomial-size circuit families decide only languages
in `P`.** This is the circuits-to-machines direction of Arora–Barak
Theorem 6.7. -/
theorem UniformPPoly_subset_P : UniformPPoly ⊆ P :=
  UniformPPoly_subset_P_internal

end Complexity
