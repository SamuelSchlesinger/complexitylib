/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Classes.PPoly.Uniform.Unrolling.Generator.Primitive.Defs

/-!
# Dynamic recent-wire offsets -- definitions

Some transition blocks need a wire whose distance behind `available` is
computed at run time. This module prepares such a reference with a bounded
binary loop and combines it with one ordinary fixed-offset reference.

The explicit distinctness records rule out aliasing between controller,
scratch, reference, and emission registers. They make preservation claims
about the dynamic offset and loop counter part of the auditable interface.
-/

@[expose] public section

namespace Complexity

namespace CircuitUnrolling

namespace Serializer

namespace DirectGenerator

/-- Pairwise separation of the reference, dynamic offset, and count-up
controller used by dynamic subtraction. -/
structure DecrementReferenceDistinct (reference offset counter : Fin WorkCount) :
    Prop where
  reference_ne_offset : reference ≠ offset
  reference_ne_counter : reference ≠ counter
  offset_ne_counter : offset ≠ counter

/-- Pairwise separation of every register used by dynamic recent-reference
preparation. -/
structure DynamicRecentDistinct (reference offset counter : Fin WorkCount) :
    Prop extends DecrementReferenceDistinct reference offset counter where
  available_ne_reference : Work.available ≠ reference
  available_ne_offset : Work.available ≠ offset
  available_ne_counter : Work.available ≠ counter
  available_ne_copyCounter : Work.available ≠ Work.copyCounter
  reference_ne_copyCounter : reference ≠ Work.copyCounter
  offset_ne_copyCounter : offset ≠ Work.copyCounter
  counter_ne_copyCounter : counter ≠ Work.copyCounter

/-- Pairwise separation of every register used by dynamic recent-gate
emission. -/
structure DynamicRecentGateDistinct (offset counter : Fin WorkCount) : Prop
    extends DynamicRecentDistinct Work.reference₀ offset counter where
  available_ne_reference₁ : Work.available ≠ Work.reference₁
  available_ne_emitCounter : Work.available ≠ Work.emitCounter
  reference₀_ne_reference₁ : Work.reference₀ ≠ Work.reference₁
  reference₀_ne_emitCounter : Work.reference₀ ≠ Work.emitCounter
  offset_ne_reference₁ : offset ≠ Work.reference₁
  offset_ne_emitCounter : offset ≠ Work.emitCounter
  counter_ne_reference₁ : counter ≠ Work.reference₁
  counter_ne_emitCounter : counter ≠ Work.emitCounter
  copyCounter_ne_reference₁ : Work.copyCounter ≠ Work.reference₁
  copyCounter_ne_emitCounter : Work.copyCounter ≠ Work.emitCounter
  reference₁_ne_emitCounter : Work.reference₁ ≠ Work.emitCounter

/-- Subtract a run-time offset from `reference` with a bounded count-up loop,
then restore its controller to zero. -/
def decrementReferenceBy (reference offset counter : Fin WorkCount) :
    BinaryRoutine WorkCount :=
  let routine := BinaryRoutine.seq
      (BinaryRoutine.binaryFor (BinaryRoutine.binaryPred reference) counter
        offset)
      (BinaryRoutine.clear counter)
  { routine with
    requires := fun values =>
      DecrementReferenceDistinct reference offset counter ∧
        values counter = 0 ∧ values offset ≤ values reference }

/-- Copy `available` into `reference`, decrement it once for every value below
the dynamic `offset`, and restore the count-up controller to zero. -/
def prepareDynamicRecentReference (reference offset counter : Fin WorkCount) :
    BinaryRoutine WorkCount :=
  let routine := BinaryRoutine.seqList
      [BinaryRoutine.binaryCopy Work.available reference Work.copyCounter,
        decrementReferenceBy reference offset counter]
  { routine with
    requires := fun values =>
      DynamicRecentDistinct reference offset counter ∧
        values Work.copyCounter = 0 ∧ values counter = 0 ∧
        values offset ≤ values Work.available }

/-- Emit a raw gate whose first input has a run-time recent-wire offset and
whose second input has a fixed recent-wire offset. -/
def emitDynamicRecentGate (op : AndOrOp) (negated₀ negated₁ : Bool)
    (offset counter : Fin WorkCount) (fixedOffset₁ : ℕ) :
    BinaryRoutine WorkCount :=
  let routine := BinaryRoutine.seqList
      [prepareDynamicRecentReference Work.reference₀ offset counter,
        prepareRecentReference Work.reference₁ fixedOffset₁,
        BinaryRoutine.emitRawGateStep op negated₀ negated₁
          Work.emitCounter Work.available Work.reference₀ Work.reference₁,
        BinaryRoutine.clear Work.reference₀,
        BinaryRoutine.clear Work.reference₁]
  { routine with
    requires := fun values =>
      DynamicRecentGateDistinct offset counter ∧
        values Work.copyCounter = 0 ∧ values counter = 0 ∧
        values offset ≤ values Work.available ∧
        fixedOffset₁ ≤ values Work.available ∧
        values Work.emitCounter = 0 }

end DirectGenerator

end Serializer

end CircuitUnrolling

end Complexity
