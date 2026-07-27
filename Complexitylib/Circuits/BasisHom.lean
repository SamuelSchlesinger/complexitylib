/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.BasisHom.Defs
public import Complexitylib.Circuits.BasisHom.Internal

/-!
# Semantics-preserving maps between circuit bases

A `Basis.Hom` relabels operations while preserving their arity and exact
Boolean semantics. Circuit transport along a homomorphism preserves semantics,
gate count, wiring, and depth exactly.
-/

@[expose] public section

namespace Complexity

namespace Gate

/-- Gate relabeling preserves evaluation exactly. -/
theorem eval_mapBasis
    (hom : Basis.Hom source target)
    (gate : Gate source W) (wireValues : BitString W) :
    (gate.mapBasis hom).eval wireValues =
      gate.eval wireValues :=
  eval_mapBasis_internal hom gate wireValues

end Gate

namespace Circuit

variable {N M G : ℕ} [NeZero N] [NeZero M]

/-- Basis transport preserves every wire value. -/
theorem wireValue_mapBasis
    (hom : Basis.Hom source target)
    (circuit : Circuit source N M G)
    (input : BitString N) (wire : Fin (N + G)) :
    (circuit.mapBasis hom).wireValue input wire =
      circuit.wireValue input wire :=
  wireValue_mapBasis_internal hom circuit input wire

/-- Basis transport preserves circuit semantics exactly. -/
theorem eval_mapBasis
    (hom : Basis.Hom source target)
    (circuit : Circuit source N M G)
    (input : BitString N) :
    (circuit.mapBasis hom).eval input =
      circuit.eval input :=
  eval_mapBasis_internal hom circuit input

/-- Basis transport preserves every wire depth. -/
theorem wireDepth_mapBasis
    (hom : Basis.Hom source target)
    (circuit : Circuit source N M G)
    (wire : Fin (N + G)) :
    (circuit.mapBasis hom).wireDepth wire =
      circuit.wireDepth wire :=
  wireDepth_mapBasis_internal hom circuit wire

/-- Basis transport preserves selected-output depth. -/
theorem outputDepth_mapBasis
    (hom : Basis.Hom source target)
    (circuit : Circuit source N M G) (output : Fin M) :
    (circuit.mapBasis hom).outputDepth output =
      circuit.outputDepth output :=
  outputDepth_mapBasis_internal hom circuit output

/-- Basis transport preserves total circuit depth. -/
theorem depth_mapBasis
    (hom : Basis.Hom source target)
    (circuit : Circuit source N M G) :
    (circuit.mapBasis hom).depth = circuit.depth :=
  depth_mapBasis_internal hom circuit

/-- Basis transport preserves the `G + M` size exactly. -/
theorem size_mapBasis
    (hom : Basis.Hom source target)
    (circuit : Circuit source N M G) :
    (circuit.mapBasis hom).size = circuit.size :=
  size_mapBasis_internal hom circuit

end Circuit

namespace CircuitFamily

/-- Basis transport preserves the computed Boolean function family. -/
theorem function_mapBasis
    (hom : Basis.Hom source target)
    (family : CircuitFamily source) :
    (family.mapBasis hom).function = family.function :=
  function_mapBasis_internal hom family

/-- Basis transport preserves the pointwise family-size function. -/
theorem size_mapBasis
    (hom : Basis.Hom source target)
    (family : CircuitFamily source) :
    (family.mapBasis hom).size = family.size :=
  size_mapBasis_internal hom family

/-- Basis transport preserves the pointwise family-depth function. -/
theorem depth_mapBasis
    (hom : Basis.Hom source target)
    (family : CircuitFamily source) :
    (family.mapBasis hom).depth = family.depth :=
  depth_mapBasis_internal hom family

end CircuitFamily
end Complexity
