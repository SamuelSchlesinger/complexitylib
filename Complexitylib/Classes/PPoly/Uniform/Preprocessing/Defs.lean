/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Encoding.Pairing

/-!
# Inputs for uniform circuit-family evaluation

The verified serialized evaluator consumes a pair of a tagged circuit code
and the circuit input. A uniformity generator consumes unary length instead.
This module names the pure preprocessing map connecting those interfaces.
-/

@[expose] public section

namespace Complexity

/-- On input `x`, run the prospective uniformity generator on `1^|x|` and
pair the resulting circuit code with the unchanged input. -/
def generatorEvalInput (gen : List Bool → List Bool) (x : List Bool) : List Bool :=
  pair (gen (List.replicate x.length true)) x

end Complexity
