/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Classes.PPoly.Uniform.Preprocessing.Defs
public import Complexitylib.Classes.PPoly.Uniform.Preprocessing.Internal

/-!
# Inputs for uniform circuit-family evaluation

## Main result

- `generatorEvalInput_mem_FP` — construct `pair (gen 1^|x|) x` in `FP`
-/

@[expose] public section

namespace Complexity

/-- A polynomial-time uniformity generator can be run on unary input length
and paired with the unchanged original input in polynomial time. -/
theorem generatorEvalInput_mem_FP {gen : List Bool → List Bool}
    (hgen : gen ∈ FP) : generatorEvalInput gen ∈ FP :=
  generatorEvalInput_mem_FP_internal hgen

end Complexity
