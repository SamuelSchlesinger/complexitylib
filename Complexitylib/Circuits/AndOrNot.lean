/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.AndOrNot.Defs
public import Complexitylib.Circuits.Internal.Simulation

/-! # AND/OR/NOT Basis

This module provides the AND/OR basis definitions and completeness results.

## Definitions (from `Complexitylib.Circuits.AndOrNot.Defs`)

* `AndOrOp` — AND/OR operations
* `Basis.unboundedAndOr` — unbounded fan-in AND/OR basis
* `Basis.boundedAndOr k` — fan-in ≤ `k` AND/OR basis
* `Basis.andOr2` — fan-in exactly 2 AND/OR basis

## Main results

* `CompleteBasis Basis.unboundedAndOr` — proved via DNF construction
* `CompleteBasis Basis.andOr2` — proved via gate-chain simulation
  from `unboundedAndOr`, using `CompleteBasis.of_simulation`
* `CompileAndOr.compileFn_eval` — exact semantics of that simulation
* `CompileAndOr.compileFn_size_le` — its quantitative size overhead
-/

@[expose] public section

namespace Complexity

namespace CompileAndOr

variable {N M G : Nat} [NeZero N] [NeZero M]

/-- Compiling unbounded fan-in AND/OR gates to fan-in two preserves the
circuit's complete multi-output semantics. -/
@[simp] theorem compileFn_eval
    (c : Circuit Basis.unboundedAndOr N M G) :
    (compileFn c).eval = c.eval :=
  compileFn_eval_internal c

/-- The compiled circuit has one public output gate for each source output,
in addition to the internal gate chains. -/
@[simp] theorem compileFn_size
    (c : Circuit Basis.unboundedAndOr N M G) :
    (compileFn c).size = G' c + M :=
  rfl

/-- Gate-chain simulation has size at most source total fan-in plus source
size plus one passthrough gate per output. -/
theorem compileFn_size_le
    (c : Circuit Basis.unboundedAndOr N M G) :
    (compileFn c).size ≤ c.totalFanIn + c.size + M :=
  compileFn_size_le_internal c

end CompileAndOr

end Complexity
