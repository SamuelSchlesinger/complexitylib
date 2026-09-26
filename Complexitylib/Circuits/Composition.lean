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
* `Circuit.eval_parallel` -- parallel composition appends output tuples.
* `Circuit.size_parallel` -- parallel composition also has exact additive size.
* `Circuit.depth_parallel` -- parallel depth is the maximum of component depths.
* `Circuit.exists_parallelFamily_depth` -- finite packing with a common depth bound.
-/


public section

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

/-! ## Parallel composition -/

/-- Parallel composition preserves every left-component wire value. -/
theorem wireValue_parallel_left
    (left : Circuit B N K G₁) (right : Circuit B N M G₂)
    (input : BitString N) (wire : Fin (N + G₁)) :
    (left.parallel right).wireValue input (embedParallelLeftWire wire) =
      left.wireValue input wire :=
  wireValue_parallel_left_internal left right input wire

/-- Parallel composition preserves every right-component wire value after
shifting its internal-gate block past the left component. -/
theorem wireValue_parallel_right
    (left : Circuit B N K G₁) (right : Circuit B N M G₂)
    (input : BitString N) (wire : Fin (N + G₂)) :
    (left.parallel right).wireValue input (embedParallelRightWire wire) =
      right.wireValue input wire :=
  wireValue_parallel_right_internal left right input wire

/-- Parallel circuit composition appends the two source output tuples. -/
@[simp] theorem eval_parallel
    (left : Circuit B N K G₁) (right : Circuit B N M G₂)
    (input : BitString N) :
    (left.parallel right).eval input =
      Fin.append (left.eval input) (right.eval input) :=
  eval_parallel_internal left right input

/-- Parallel composition has exactly additive size: it shares primary inputs
and otherwise preserves every internal and output gate. -/
@[simp] theorem size_parallel
    (left : Circuit B N K G₁) (right : Circuit B N M G₂) :
    (left.parallel right).size = left.size + right.size :=
  size_parallel_internal left right

/-- Any positive finite family of single-output circuits with shared primary
inputs can be packed into one multi-output circuit. Its size is exactly the sum
of the source sizes, and output `i` is the output of source circuit `i`. -/
theorem exists_parallelFamily {count : ℕ} [NeZero count]
    (circuits : Fin count →
      Σ internalGates, Circuit B N 1 internalGates) :
    ∃ internalGates,
      ∃ packed : Circuit B N count internalGates,
        packed.size = (∑ i, ((circuits i).2).size) ∧
          ∀ input i,
            packed.eval input i = ((circuits i).2.eval input) 0 :=
  exists_parallelFamily_internal circuits

/-- Parallel composition preserves every left-component wire depth. -/
theorem wireDepth_parallel_left
    (left : Circuit B N K G₁) (right : Circuit B N M G₂) (wire : Fin (N + G₁)) :
    (left.parallel right).wireDepth (embedParallelLeftWire wire) = left.wireDepth wire :=
  wireDepth_parallel_left_internal left right wire

/-- Parallel composition preserves every right-component wire depth. -/
theorem wireDepth_parallel_right
    (left : Circuit B N K G₁) (right : Circuit B N M G₂) (wire : Fin (N + G₂)) :
    (left.parallel right).wireDepth (embedParallelRightWire wire) = right.wireDepth wire :=
  wireDepth_parallel_right_internal left right wire

/-- Parallel composition preserves depth exactly as the maximum of the two depths. -/
theorem depth_parallel (left : Circuit B N K G₁) (right : Circuit B N M G₂) :
    (left.parallel right).depth = max left.depth right.depth :=
  depth_parallel_internal left right

/-- A finite family can be packed without increasing a common depth bound. -/
theorem exists_parallelFamily_depth {count : Nat} [NeZero count]
    (circuits : Fin count → Σ gates, Circuit B N 1 gates) (d : Nat)
    (hdepth : ∀ i, (circuits i).2.depth ≤ d) :
    ∃ gates, ∃ packed : Circuit B N count gates,
      packed.size = (∑ i, (circuits i).2.size) ∧ packed.depth ≤ d ∧
        ∀ input i, packed.eval input i = ((circuits i).2.eval input) 0 :=
  exists_parallelFamily_depth_internal circuits d hdepth

end Circuit

end Complexity
