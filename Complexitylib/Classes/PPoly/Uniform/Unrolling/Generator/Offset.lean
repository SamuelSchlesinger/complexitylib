/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Classes.PPoly.Uniform.Unrolling.Generator.Offset.Defs
public import Complexitylib.Classes.PPoly.Uniform.Unrolling.Generator.Offset.Internal

/-!
# Dynamic recent-wire offsets

Proof-carrying helpers for subtracting a run-time wire offset and emitting a
raw gate with one dynamic and one fixed recent-wire reference.
-/

@[expose] public section

namespace Complexity

namespace CircuitUnrolling

namespace Serializer

namespace DirectGenerator

/-- Dynamic reference subtraction is sound on its explicit domain. -/
theorem decrementReferenceBy_sound (reference offset counter : Fin WorkCount) :
    (decrementReferenceBy reference offset counter).Sound :=
  decrementReferenceBy_sound_internal reference offset counter

/-- Dynamic subtraction has a pointwise width certificate when its controller
segment, starting reference, and preserved offset all fit the shared width. -/
theorem decrementReferenceBy_spaceBoundByWidth
    (reference offset counter : Fin WorkCount)
    (hdistinct : DecrementReferenceDistinct reference offset counter)
    {initialSpace : ℕ → ℕ} {values : ℕ → BinaryValues WorkCount}
    {width : ℕ → ℕ}
    (hcounterOffset : ∀ inputLength,
      values inputLength counter ≤ values inputLength offset)
    (hiterationsFit : ∀ inputLength,
      values inputLength offset - values inputLength counter ≤
        values inputLength reference)
    (hreference : ∀ inputLength,
      values inputLength reference ≤ width inputLength)
    (hoffset : ∀ inputLength,
      values inputLength offset ≤ width inputLength) :
    BinaryRoutine.SpaceBoundByWidthAt
      (decrementReferenceBy reference offset counter) initialSpace values
      width :=
  decrementReferenceBy_spaceBoundByWidth_internal reference offset counter
    hdistinct hcounterOffset hiterationsFit hreference hoffset

/-- The subtraction domain explicitly requires distinct registers, a zero
controller, and an offset no larger than the starting reference. -/
theorem decrementReferenceBy_requires (reference offset counter : Fin WorkCount)
    (values : BinaryValues WorkCount) :
    (decrementReferenceBy reference offset counter).requires values ↔
      DecrementReferenceDistinct reference offset counter ∧
        values counter = 0 ∧ values offset ≤ values reference :=
  decrementReferenceBy_requires_internal reference offset counter values

/-- Exact dynamic subtraction with the count-up controller restored to zero. -/
theorem decrementReferenceBy_effect (reference offset counter : Fin WorkCount)
    (values : BinaryValues WorkCount)
    (hdistinct : DecrementReferenceDistinct reference offset counter)
    (hcounter : values counter = 0) :
    (decrementReferenceBy reference offset counter).effect values =
      Function.update
        (Function.update values reference
          (values reference - values offset)) counter 0 :=
  decrementReferenceBy_effect_internal reference offset counter values
    hdistinct hcounter

/-- Dynamic subtraction emits no circuit-code bits. -/
@[simp] theorem decrementReferenceBy_emitted
    (reference offset counter : Fin WorkCount)
    (values : BinaryValues WorkCount) :
    (decrementReferenceBy reference offset counter).emitted values = [] :=
  decrementReferenceBy_emitted_internal reference offset counter values

/-- Dynamic recent-reference preparation is sound on its explicit domain. -/
theorem prepareDynamicRecentReference_sound
    (reference offset counter : Fin WorkCount) :
    (prepareDynamicRecentReference reference offset counter).Sound :=
  prepareDynamicRecentReference_sound_internal reference offset counter

/-- Dynamic recent-reference preparation has a pointwise width certificate
when the available wire, old destination, zero controller, and offset fit the
shared width. -/
theorem prepareDynamicRecentReference_spaceBoundByWidth
    (reference offset counter : Fin WorkCount)
    (hdistinct : DynamicRecentDistinct reference offset counter)
    {initialSpace : ℕ → ℕ} {values : ℕ → BinaryValues WorkCount}
    {width : ℕ → ℕ}
    (havailable : ∀ inputLength,
      values inputLength Work.available ≤ width inputLength)
    (hreference : ∀ inputLength,
      values inputLength reference ≤ width inputLength)
    (hcounter : ∀ inputLength, values inputLength counter = 0)
    (hoffset : ∀ inputLength,
      values inputLength offset ≤ values inputLength Work.available) :
    BinaryRoutine.SpaceBoundByWidthAt
      (prepareDynamicRecentReference reference offset counter)
      initialSpace values width :=
  prepareDynamicRecentReference_spaceBoundByWidth_internal reference offset
    counter hdistinct havailable hreference hcounter hoffset

/-- The preparation domain records every register separation, both zero
controllers, and the valid dynamic offset. -/
theorem prepareDynamicRecentReference_requires
    (reference offset counter : Fin WorkCount)
    (values : BinaryValues WorkCount) :
    (prepareDynamicRecentReference reference offset counter).requires values ↔
      DynamicRecentDistinct reference offset counter ∧
        values Work.copyCounter = 0 ∧ values counter = 0 ∧
        values offset ≤ values Work.available :=
  prepareDynamicRecentReference_requires_internal reference offset counter
    values

/-- Exact dynamic recent-wire reference with its controller restored to zero. -/
theorem prepareDynamicRecentReference_effect
    (reference offset counter : Fin WorkCount)
    (values : BinaryValues WorkCount)
    (hdistinct : DynamicRecentDistinct reference offset counter)
    (hcounter : values counter = 0) :
    (prepareDynamicRecentReference reference offset counter).effect values =
      Function.update
        (Function.update values reference
          (values Work.available - values offset)) counter 0 :=
  prepareDynamicRecentReference_effect_internal reference offset counter values
    hdistinct hcounter

/-- Dynamic recent-reference preparation emits no circuit-code bits. -/
@[simp] theorem prepareDynamicRecentReference_emitted
    (reference offset counter : Fin WorkCount)
    (values : BinaryValues WorkCount) :
    (prepareDynamicRecentReference reference offset counter).emitted values =
      [] :=
  prepareDynamicRecentReference_emitted_internal reference offset counter values

/-- One-dynamic-offset raw-gate emission is sound. -/
theorem emitDynamicRecentGate_sound (op : AndOrOp)
    (negated₀ negated₁ : Bool) (offset counter : Fin WorkCount)
    (fixedOffset₁ : ℕ) :
    (emitDynamicRecentGate op negated₀ negated₁ offset counter
        fixedOffset₁).Sound :=
  emitDynamicRecentGate_sound_internal op negated₀ negated₁ offset counter
    fixedOffset₁

/-- One-dynamic-offset gate emission has a pointwise width certificate when
its wire frontier, references, zero controller, and both offsets fit the
shared width. -/
theorem emitDynamicRecentGate_spaceBoundByWidth
    (op : AndOrOp) (negated₀ negated₁ : Bool)
    (offset counter : Fin WorkCount) (fixedOffset₁ : ℕ)
    (hdistinct : DynamicRecentGateDistinct offset counter)
    {initialSpace : ℕ → ℕ} {values : ℕ → BinaryValues WorkCount}
    {width : ℕ → ℕ}
    (havailable : ∀ inputLength,
      values inputLength Work.available ≤ width inputLength)
    (hreference₀ : ∀ inputLength,
      values inputLength Work.reference₀ ≤ width inputLength)
    (hreference₁ : ∀ inputLength,
      values inputLength Work.reference₁ ≤ width inputLength)
    (hcounter : ∀ inputLength, values inputLength counter = 0)
    (hoffset : ∀ inputLength,
      values inputLength offset ≤ values inputLength Work.available)
    (hfixedOffset₁ : ∀ inputLength,
      fixedOffset₁ ≤ values inputLength Work.available) :
    BinaryRoutine.SpaceBoundByWidthAt
      (emitDynamicRecentGate op negated₀ negated₁ offset counter
        fixedOffset₁) initialSpace values width :=
  emitDynamicRecentGate_spaceBoundByWidth_internal op negated₀ negated₁
    offset counter fixedOffset₁ hdistinct havailable hreference₀ hreference₁
    hcounter hoffset hfixedOffset₁

/-- Exact domain for one-dynamic-offset raw-gate emission. -/
theorem emitDynamicRecentGate_requires (op : AndOrOp)
    (negated₀ negated₁ : Bool) (offset counter : Fin WorkCount)
    (fixedOffset₁ : ℕ) (values : BinaryValues WorkCount) :
    (emitDynamicRecentGate op negated₀ negated₁ offset counter
        fixedOffset₁).requires values ↔
      DynamicRecentGateDistinct offset counter ∧
        values Work.copyCounter = 0 ∧ values counter = 0 ∧
        values offset ≤ values Work.available ∧
        fixedOffset₁ ≤ values Work.available ∧
        values Work.emitCounter = 0 :=
  emitDynamicRecentGate_requires_internal op negated₀ negated₁ offset
    counter fixedOffset₁ values

/-- Dynamic recent-gate emission advances `available`, restores the loop
controller, and clears both reference tapes. -/
theorem emitDynamicRecentGate_effect (op : AndOrOp)
    (negated₀ negated₁ : Bool) (offset counter : Fin WorkCount)
    (fixedOffset₁ : ℕ) (values : BinaryValues WorkCount)
    (hdistinct : DynamicRecentGateDistinct offset counter)
    (hcounter : values counter = 0) :
    (emitDynamicRecentGate op negated₀ negated₁ offset counter
        fixedOffset₁).effect values =
      Function.update
        (Function.update
          (Function.update
            (Function.update values counter 0) Work.available
              (values Work.available + 1)) Work.reference₀ 0)
        Work.reference₁ 0 :=
  emitDynamicRecentGate_effect_internal op negated₀ negated₁ offset
    counter fixedOffset₁ values hdistinct hcounter

/-- Exact raw gate emitted from the dynamic and fixed recent-wire offsets. -/
theorem emitDynamicRecentGate_emitted (op : AndOrOp)
    (negated₀ negated₁ : Bool) (offset counter : Fin WorkCount)
    (fixedOffset₁ : ℕ) (values : BinaryValues WorkCount)
    (hdistinct : DynamicRecentGateDistinct offset counter)
    (hcounter : values counter = 0) :
    (emitDynamicRecentGate op negated₀ negated₁ offset counter
        fixedOffset₁).emitted values =
      CircuitCode.RawGate.encode
        { op := op
          input₀ := values Work.available - values offset
          input₁ := values Work.available - fixedOffset₁
          negated₀ := negated₀
          negated₁ := negated₁ } :=
  emitDynamicRecentGate_emitted_internal op negated₀ negated₁ offset
    counter fixedOffset₁ values hdistinct hcounter

end DirectGenerator

end Serializer

end CircuitUnrolling

end Complexity
