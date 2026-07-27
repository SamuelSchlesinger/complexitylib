/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.Composition.Defs
public import Complexitylib.Circuits.Composition.Internal

/-!
# Resource-accounted circuit composition

This module exposes serial composition of two circuits over the same basis.
The construction shares every inner output and therefore has exact additive
size, rather than duplicating the inner circuit once per outer use.

## Main results

* `Circuit.eval_compose` -- exact functional composition.
* `Circuit.size_compose` -- exact additive size.
* `Circuit.depth_compose_le` -- depth is at most the sum of source depths.
-/

@[expose] public section

namespace Complexity

namespace Gate

/-- Rewiring a gate composes its wire-value assignment with the wire map. -/
theorem eval_rewire {B : Basis} {W W' : ℕ}
    (gate : Gate B W) (mapWire : Fin W → Fin W')
    (wireValue : BitString W') :
    (gate.rewire mapWire).eval wireValue =
      gate.eval fun wire => wireValue (mapWire wire) :=
  eval_rewire_internal gate mapWire wireValue

end Gate

namespace Circuit

variable {B : Basis} {N K M G₁ G₂ : ℕ}
  [NeZero N] [NeZero K] [NeZero M]

/-- Composition preserves each original inner wire value. -/
theorem wireValue_compose_inner
    (outer : Circuit B K M G₂) (inner : Circuit B N K G₁)
    (input : BitString N) (wire : Fin (N + G₁)) :
    (outer.compose inner).wireValue input (embedInnerWire wire) =
      inner.wireValue input wire :=
  wireValue_compose_inner_internal outer inner input wire

/-- A materialized inner-output wire carries the corresponding inner result. -/
theorem wireValue_compose_innerOutput
    (outer : Circuit B K M G₂) (inner : Circuit B N K G₁)
    (input : BitString N) (output : Fin K) :
    (outer.compose inner).wireValue input (embedInnerOutput output) =
      inner.eval input output :=
  wireValue_compose_innerOutput_internal outer inner input output

/-- Composition preserves outer wire semantics after feeding the inner
circuit's result to the outer circuit. -/
theorem wireValue_compose_outer
    (outer : Circuit B K M G₂) (inner : Circuit B N K G₁)
    (input : BitString N) (wire : Fin (K + G₂)) :
    (outer.compose inner).wireValue input (embedOuterWire wire) =
      outer.wireValue (inner.eval input) wire :=
  wireValue_compose_outer_internal outer inner input wire

/-- Composition preserves the depth of every original inner wire. -/
theorem wireDepth_compose_inner
    (outer : Circuit B K M G₂) (inner : Circuit B N K G₁)
    (wire : Fin (N + G₁)) :
    (outer.compose inner).wireDepth (embedInnerWire wire) =
      inner.wireDepth wire :=
  wireDepth_compose_inner_internal outer inner wire

/-- A materialized inner output has exactly its original output depth. -/
theorem wireDepth_compose_innerOutput
    (outer : Circuit B K M G₂) (inner : Circuit B N K G₁)
    (output : Fin K) :
    (outer.compose inner).wireDepth (embedInnerOutput output) =
      inner.outputDepth output :=
  wireDepth_compose_innerOutput_internal outer inner output

/-- Every embedded outer wire has depth at most the inner circuit depth plus
its original outer-circuit wire depth. -/
theorem wireDepth_compose_outer_le
    (outer : Circuit B K M G₂) (inner : Circuit B N K G₁)
    (wire : Fin (K + G₂)) :
    (outer.compose inner).wireDepth (embedOuterWire wire) ≤
      inner.depth + outer.wireDepth wire :=
  wireDepth_compose_outer_le_internal outer inner wire

/-- Serial circuit composition agrees exactly with function composition. -/
@[simp] theorem eval_compose
    (outer : Circuit B K M G₂) (inner : Circuit B N K G₁)
    (input : BitString N) :
    (outer.compose inner).eval input =
      outer.eval (inner.eval input) :=
  eval_compose_internal outer inner input

/-- Serial composition has exactly additive size under the library convention.
The `K` inner output gates become internal gates, so no output gate is lost or
double-counted. -/
@[simp] theorem size_compose
    (outer : Circuit B K M G₂) (inner : Circuit B N K G₁) :
    (outer.compose inner).size = inner.size + outer.size := by
  simp only [Circuit.size]
  omega

/-- Serial composition adds at most the two source depths. -/
theorem depth_compose_le
    (outer : Circuit B K M G₂) (inner : Circuit B N K G₁) :
    (outer.compose inner).depth ≤ inner.depth + outer.depth :=
  depth_compose_le_internal outer inner

end Circuit

end Complexity
