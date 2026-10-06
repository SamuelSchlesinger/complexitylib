/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.DepthClasses
public import Complexitylib.Circuits.Threshold.Parity
public import Complexitylib.Circuits.XOR
public import Complexitylib.Circuits.AC0.Separation.Internal

/-!
# Parity is not in `AC0`, and `AC0 ⊂ TC0`

The parity family `Schnorr.xorBool` is not in the library's nonuniform `AC0`:
no family of polynomial-size, constant-depth, unbounded-fan-in AND/OR circuits
with free negation on gate inputs computes parity at every input length.

The proof normalizes each circuit to a negation-normal formula of no larger
depth and polynomial size (`Circuit.outputAC0Formula_spec`) and contradicts the
finite iterated-switching obstruction (`AC0Formula.parity_counting_obstruction`)
at one explicit large input length. The quantitative bound obtained this way is
far from Håstad's; only the separation is stated.

Since parity is in `TC0` (`xorBool_mem_TC0`) and `AC0 ⊆ TC0`, the inclusion is
strict.
-/


public section

namespace Complexity

/-- **Parity is not in `AC0`.** No polynomial-size, constant-depth family of
unbounded-fan-in AND/OR circuits computes the parity family. -/
theorem xorBool_not_mem_AC0 : Schnorr.xorBool ∉ AC0 :=
  xorBool_not_mem_AC0_internal

/-- **`AC0` is strictly contained in `TC0`**, as nonuniform classes of Boolean
function families. Parity separates them. -/
theorem AC0_ssubset_TC0 : AC0 ⊂ TC0 :=
  Set.ssubset_iff_subset_ne.mpr
    ⟨AC0_subset_TC0, fun h => xorBool_not_mem_AC0 (h ▸ xorBool_mem_TC0)⟩

end Complexity
