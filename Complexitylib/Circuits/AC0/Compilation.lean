/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.AC0.Compilation.Defs
public import Complexitylib.Circuits.AC0.Compilation.Internal

/-!
# Circuit realizations of unbounded formula trees

Every `AC0Formula` over a positive input width has an equivalent circuit over
`Basis.unboundedAndOr` with exactly the same size and depth at most one greater.
The extra layer accounts for the circuit model's counted output gates at leaves.
Empty connectives are realized by nullary gates.

This is a finite existence theorem. It imposes no uniformity condition on a
family of circuits chosen at different input lengths.
-/

public section

namespace Complexity.AC0Formula

/-- An unbounded formula has a circuit realization with exact size and at most
one extra depth layer, including constants and empty connectives. -/
theorem exists_circuit {N : Nat} [NeZero N] (f : AC0Formula N) :
    ∃ gates, ∃ c : Circuit Basis.unboundedAndOr N 1 gates,
      c.size = f.size ∧ c.depth ≤ f.depth + 1 ∧
        ∀ input, c.eval input 0 = f.eval input :=
  exists_circuit_internal f

end Complexity.AC0Formula
