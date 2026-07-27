/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Classes.PPoly.Uniform.Unrolling.Generator.Primitive.Defs
public import Complexitylib.Classes.PPoly.Uniform.Unrolling.Generator.Primitive.Internal

/-!
# Direct-unrolling generator primitives

Executable fixed-work helpers for recent-wire raw gates and numeric state,
head, and cell configuration-wire references.
-/

@[expose] public section

namespace Complexity

namespace CircuitUnrolling

namespace Serializer

namespace DirectGenerator

/-- Fixed-offset preparation by copy and repeated positive predecessor is
sound on its explicit routine domain. -/
theorem prepareRecentReference_sound (reference : Fin WorkCount) (offset : ℕ) :
    (prepareRecentReference reference offset).Sound :=
  prepareRecentReference_sound_internal reference offset

/-- Fixed-offset recent-reference preparation has a pointwise width
certificate when the source, old destination, and requested offset fit the
shared width. -/
theorem prepareRecentReference_spaceBoundByWidth
    (reference : Fin WorkCount) (offset : ℕ)
    {initialSpace : ℕ → ℕ} {values : ℕ → BinaryValues WorkCount}
    {width : ℕ → ℕ}
    (havailable : ∀ inputLength,
      values inputLength Work.available ≤ width inputLength)
    (hreference : ∀ inputLength,
      values inputLength reference ≤ width inputLength)
    (hoffset : ∀ inputLength,
      offset ≤ values inputLength Work.available) :
    BinaryRoutine.SpaceBoundByWidthAt (prepareRecentReference reference offset)
      initialSpace values width :=
  prepareRecentReference_spaceBoundByWidth_internal reference offset
    havailable hreference hoffset

/-- The recent-reference domain is exactly a zero copy counter and a valid
offset, once the three framed-copy indices are known to be distinct. -/
theorem prepareRecentReference_requires (reference : Fin WorkCount)
    (offset : ℕ) (values : BinaryValues WorkCount)
    (havailableReference : Work.available ≠ reference)
    (havailableCounter : Work.available ≠ Work.copyCounter)
    (hreferenceCounter : reference ≠ Work.copyCounter) :
    (prepareRecentReference reference offset).requires values ↔
      values Work.copyCounter = 0 ∧ offset ≤ values Work.available :=
  prepareRecentReference_requires_internal reference offset values
    havailableReference havailableCounter hreferenceCounter

/-- Exact fixed-offset reference value. -/
@[simp] theorem prepareRecentReference_effect (reference : Fin WorkCount)
    (offset : ℕ) (values : BinaryValues WorkCount) :
    (prepareRecentReference reference offset).effect values =
      Function.update values reference (values Work.available - offset) :=
  prepareRecentReference_effect_internal reference offset values

/-- Reference preparation emits no circuit-code bits. -/
@[simp] theorem prepareRecentReference_emitted (reference : Fin WorkCount)
    (offset : ℕ) (values : BinaryValues WorkCount) :
    (prepareRecentReference reference offset).emitted values = [] :=
  prepareRecentReference_emitted_internal reference offset values

/-- A raw gate from two recent-wire offsets is sound. -/
theorem emitRecentGate_sound (op : AndOrOp) (negated₀ negated₁ : Bool)
    (offset₀ offset₁ : ℕ) :
    (emitRecentGate op negated₀ negated₁ offset₀ offset₁).Sound :=
  emitRecentGate_sound_internal op negated₀ negated₁ offset₀ offset₁

/-- A raw gate from two fixed recent-wire offsets has a pointwise width
certificate when the frontier, old references, and offsets fit the shared
width. -/
theorem emitRecentGate_spaceBoundByWidth
    (op : AndOrOp) (negated₀ negated₁ : Bool) (offset₀ offset₁ : ℕ)
    {initialSpace : ℕ → ℕ} {values : ℕ → BinaryValues WorkCount}
    {width : ℕ → ℕ}
    (havailable : ∀ inputLength,
      values inputLength Work.available ≤ width inputLength)
    (hreference₀ : ∀ inputLength,
      values inputLength Work.reference₀ ≤ width inputLength)
    (hreference₁ : ∀ inputLength,
      values inputLength Work.reference₁ ≤ width inputLength)
    (hoffset₀ : ∀ inputLength,
      offset₀ ≤ values inputLength Work.available)
    (hoffset₁ : ∀ inputLength,
      offset₁ ≤ values inputLength Work.available) :
    BinaryRoutine.SpaceBoundByWidthAt
      (emitRecentGate op negated₀ negated₁ offset₀ offset₁)
      initialSpace values width :=
  emitRecentGate_spaceBoundByWidth_internal op negated₀ negated₁ offset₀
    offset₁ havailable hreference₀ hreference₁ hoffset₀ hoffset₁

/-- Exact dynamic domain for recent-wire gate emission. -/
theorem emitRecentGate_requires (op : AndOrOp) (negated₀ negated₁ : Bool)
    (offset₀ offset₁ : ℕ) (values : BinaryValues WorkCount) :
    (emitRecentGate op negated₀ negated₁ offset₀ offset₁).requires
        values ↔
      values Work.copyCounter = 0 ∧
        offset₀ ≤ values Work.available ∧
        offset₁ ≤ values Work.available ∧
        values Work.emitCounter = 0 :=
  emitRecentGate_requires_internal op negated₀ negated₁ offset₀ offset₁
    values

/-- Recent-wire gate emission advances `available` once and clears both
reference tapes. -/
@[simp] theorem emitRecentGate_effect (op : AndOrOp)
    (negated₀ negated₁ : Bool) (offset₀ offset₁ : ℕ)
    (values : BinaryValues WorkCount) :
    (emitRecentGate op negated₀ negated₁ offset₀ offset₁).effect
        values =
      Function.update
        (Function.update
          (Function.update values Work.available (values Work.available + 1))
          Work.reference₀ 0) Work.reference₁ 0 :=
  emitRecentGate_effect_internal op negated₀ negated₁ offset₀ offset₁ values

/-- Exact raw gate emitted from the two prepared recent-wire references. -/
@[simp] theorem emitRecentGate_emitted (op : AndOrOp)
    (negated₀ negated₁ : Bool) (offset₀ offset₁ : ℕ)
    (values : BinaryValues WorkCount) :
    (emitRecentGate op negated₀ negated₁ offset₀ offset₁).emitted
        values =
      CircuitCode.RawGate.encode
        { op := op
          input₀ := values Work.available - offset₀
          input₁ := values Work.available - offset₁
          negated₀ := negated₀
          negated₁ := negated₁ } :=
  emitRecentGate_emitted_internal op negated₀ negated₁ offset₀ offset₁ values

/-- Numeric state-reference preparation is sound. -/
theorem prepareStateReference_sound (stateIndex : ℕ) :
    (prepareStateReference stateIndex).Sound :=
  prepareStateReference_sound_internal stateIndex

/-- State-reference preparation needs exactly its framed addition counter. -/
theorem prepareStateReference_requires (stateIndex : ℕ)
    (values : BinaryValues WorkCount) :
    (prepareStateReference stateIndex).requires values ↔
      values Work.addCounter = 0 :=
  prepareStateReference_requires_internal stateIndex values

/-- Exact numeric state-wire reference. -/
@[simp] theorem prepareStateReference_effect (stateIndex : ℕ)
    (values : BinaryValues WorkCount) :
    (prepareStateReference stateIndex).effect values =
      Function.update values Work.reference₀
        (transitionStateRef (values Work.configBase) stateIndex) :=
  prepareStateReference_effect_internal stateIndex values

/-- State-reference preparation emits nothing. -/
@[simp] theorem prepareStateReference_emitted (stateIndex : ℕ)
    (values : BinaryValues WorkCount) :
    (prepareStateReference stateIndex).emitted values = [] :=
  prepareStateReference_emitted_internal stateIndex values

/-- Numeric head-reference preparation is sound. -/
theorem prepareHeadReference_sound (stateCount : ℕ) :
    (prepareHeadReference stateCount).Sound :=
  prepareHeadReference_sound_internal stateCount

/-- Zero framed arithmetic counters discharge the complete head-reference
domain. -/
theorem prepareHeadReference_requires (stateCount : ℕ)
    (values : BinaryValues WorkCount)
    (hadd : values Work.addCounter = 0)
    (hmultiply : values Work.multiplyCounter = 0) :
    (prepareHeadReference stateCount).requires values :=
  prepareHeadReference_requires_internal stateCount values hadd hmultiply

/-- Exact numeric head-wire reference, with its arithmetic temporary cleared. -/
@[simp] theorem prepareHeadReference_effect (stateCount : ℕ)
    (values : BinaryValues WorkCount) :
    (prepareHeadReference stateCount).effect values =
      Function.update
        (Function.update values Work.reference₀
          (transitionHeadRef stateCount (values Work.horizon)
            (values Work.configBase) (values Work.tapeIndex)
            (values Work.position))) Work.temporary₀ 0 :=
  prepareHeadReference_effect_internal stateCount values

/-- Head-reference preparation emits nothing. -/
@[simp] theorem prepareHeadReference_emitted (stateCount : ℕ)
    (values : BinaryValues WorkCount) :
    (prepareHeadReference stateCount).emitted values = [] :=
  prepareHeadReference_emitted_internal stateCount values

/-- Numeric cell-reference preparation is sound. -/
theorem prepareCellReference_sound (stateCount tapeCount : ℕ) :
    (prepareCellReference stateCount tapeCount).Sound :=
  prepareCellReference_sound_internal stateCount tapeCount

/-- Zero copy, addition, and multiplication counters discharge the complete
cell-reference domain. -/
theorem prepareCellReference_requires (stateCount tapeCount : ℕ)
    (values : BinaryValues WorkCount)
    (hcopy : values Work.copyCounter = 0)
    (hadd : values Work.addCounter = 0)
    (hmultiply : values Work.multiplyCounter = 0) :
    (prepareCellReference stateCount tapeCount).requires values :=
  prepareCellReference_requires_internal stateCount tapeCount values hcopy hadd
    hmultiply

/-- Exact numeric cell-symbol wire reference, with all three arithmetic
temporaries cleared. -/
@[simp] theorem prepareCellReference_effect (stateCount tapeCount : ℕ)
    (values : BinaryValues WorkCount) :
    (prepareCellReference stateCount tapeCount).effect values =
      Function.update
        (Function.update
          (Function.update
            (Function.update values Work.reference₀
              (transitionCellRef stateCount tapeCount (values Work.horizon)
                (values Work.configBase) (values Work.tapeIndex)
                (values Work.position) (values Work.symbolIndex)))
            Work.temporary₀ 0) Work.temporary₁ 0) Work.temporary₂ 0 :=
  prepareCellReference_effect_internal stateCount tapeCount values

/-- Cell-reference preparation emits nothing. -/
@[simp] theorem prepareCellReference_emitted (stateCount tapeCount : ℕ)
    (values : BinaryValues WorkCount) :
    (prepareCellReference stateCount tapeCount).emitted values = [] :=
  prepareCellReference_emitted_internal stateCount tapeCount values

/-- Any sound preparation routine composes soundly with prepared-reference
copy emission. -/
theorem emitPreparedReference_sound {prepare : BinaryRoutine WorkCount}
    (hprepare : prepare.Sound) (negated : Bool) :
    (emitPreparedReference prepare negated).Sound :=
  emitPreparedReference_sound_internal hprepare negated

/-- Prepared numeric state-reference emission is sound. -/
theorem emitStateReference_sound (stateIndex : ℕ) (negated : Bool) :
    (emitStateReference stateIndex negated).Sound :=
  emitStateReference_sound_internal stateIndex negated

/-- Prepared numeric head-reference emission is sound. -/
theorem emitHeadReference_sound (stateCount : ℕ) (negated : Bool) :
    (emitHeadReference stateCount negated).Sound :=
  emitHeadReference_sound_internal stateCount negated

/-- Prepared numeric cell-reference emission is sound. -/
theorem emitCellReference_sound (stateCount tapeCount : ℕ)
    (negated : Bool) :
    (emitCellReference stateCount tapeCount negated).Sound :=
  emitCellReference_sound_internal stateCount tapeCount negated

/-- State-reference emission has a pointwise width certificate when every
incoming register and the resulting absolute reference fit the width. -/
theorem emitStateReference_spaceBoundByWidth
    (stateIndex : ℕ) (negated : Bool) {initialSpace : ℕ → ℕ}
    {values : ℕ → BinaryValues WorkCount} {width : ℕ → ℕ}
    (hvalues : ∀ inputLength index,
      values inputLength index ≤ width inputLength)
    (hcap : ∀ inputLength,
      transitionStateRef (values inputLength Work.configBase) stateIndex ≤
        width inputLength) :
    BinaryRoutine.SpaceBoundByWidthAt
      (emitStateReference stateIndex negated) initialSpace values width :=
  emitStateReference_spaceBoundByWidth_internal stateIndex negated hvalues hcap

/-- Head-reference emission has a pointwise width certificate under one
envelope covering all arithmetic intermediates. -/
theorem emitHeadReference_spaceBoundByWidth
    (stateCount : ℕ) (negated : Bool) {initialSpace : ℕ → ℕ}
    {values : ℕ → BinaryValues WorkCount} {width : ℕ → ℕ}
    (hvalues : ∀ inputLength index,
      values inputLength index ≤ width inputLength)
    (hcap : ∀ inputLength,
      transitionHeadRef stateCount (values inputLength Work.horizon)
          (values inputLength Work.configBase)
          (values inputLength Work.tapeIndex)
          (values inputLength Work.position) +
          values inputLength Work.tapeIndex +
          values inputLength Work.horizon + 1 ≤
        width inputLength) :
    BinaryRoutine.SpaceBoundByWidthAt
      (emitHeadReference stateCount negated) initialSpace values width :=
  emitHeadReference_spaceBoundByWidth_internal stateCount negated hvalues hcap

/-- Cell-reference emission has a pointwise width certificate under one
envelope covering its base, offset, and final-reference arithmetic. -/
theorem emitCellReference_spaceBoundByWidth
    (stateCount tapeCount : ℕ) (negated : Bool)
    {initialSpace : ℕ → ℕ} {values : ℕ → BinaryValues WorkCount}
    {width : ℕ → ℕ}
    (hvalues : ∀ inputLength index,
      values inputLength index ≤ width inputLength)
    (hcap : ∀ inputLength,
      transitionCellRef stateCount tapeCount
          (values inputLength Work.horizon)
          (values inputLength Work.configBase)
          (values inputLength Work.tapeIndex)
          (values inputLength Work.position)
          (values inputLength Work.symbolIndex) +
          (values inputLength Work.tapeIndex *
                (values inputLength Work.horizon + 2) +
              values inputLength Work.position) +
          (values inputLength Work.horizon + 2) + tapeCount +
          values inputLength Work.tapeIndex + 4 ≤
        width inputLength) :
    BinaryRoutine.SpaceBoundByWidthAt
      (emitCellReference stateCount tapeCount negated) initialSpace values
      width :=
  emitCellReference_spaceBoundByWidth_internal stateCount tapeCount negated
    hvalues hcap

/-- Zero addition and emission counters discharge state-reference emission. -/
theorem emitStateReference_requires (stateIndex : ℕ) (negated : Bool)
    (values : BinaryValues WorkCount)
    (hadd : values Work.addCounter = 0)
    (hemit : values Work.emitCounter = 0) :
    (emitStateReference stateIndex negated).requires values :=
  emitStateReference_requires_internal stateIndex negated values hadd hemit

/-- Zero arithmetic and emission counters discharge head-reference emission. -/
theorem emitHeadReference_requires (stateCount : ℕ) (negated : Bool)
    (values : BinaryValues WorkCount)
    (hadd : values Work.addCounter = 0)
    (hmultiply : values Work.multiplyCounter = 0)
    (hemit : values Work.emitCounter = 0) :
    (emitHeadReference stateCount negated).requires values :=
  emitHeadReference_requires_internal stateCount negated values hadd hmultiply hemit

/-- Zero arithmetic, copy, and emission counters discharge cell-reference
emission. -/
theorem emitCellReference_requires (stateCount tapeCount : ℕ)
    (negated : Bool) (values : BinaryValues WorkCount)
    (hcopy : values Work.copyCounter = 0)
    (hadd : values Work.addCounter = 0)
    (hmultiply : values Work.multiplyCounter = 0)
    (hemit : values Work.emitCounter = 0) :
    (emitCellReference stateCount tapeCount negated).requires values :=
  emitCellReference_requires_internal stateCount tapeCount negated values hcopy
    hadd hmultiply hemit

/-- State-reference emission advances `available` and clears the reference. -/
@[simp] theorem emitStateReference_effect (stateIndex : ℕ)
    (negated : Bool) (values : BinaryValues WorkCount) :
    (emitStateReference stateIndex negated).effect values =
      Function.update
        (Function.update values Work.available (values Work.available + 1))
        Work.reference₀ 0 :=
  emitStateReference_effect_internal stateIndex negated values

/-- Head-reference emission advances `available` and clears both scratches. -/
@[simp] theorem emitHeadReference_effect (stateCount : ℕ)
    (negated : Bool) (values : BinaryValues WorkCount) :
    (emitHeadReference stateCount negated).effect values =
      Function.update
        (Function.update
          (Function.update values Work.temporary₀ 0) Work.available
            (values Work.available + 1)) Work.reference₀ 0 :=
  emitHeadReference_effect_internal stateCount negated values

/-- Cell-reference emission advances `available` and clears all four
reference/arithmetic scratch tapes. -/
@[simp] theorem emitCellReference_effect (stateCount tapeCount : ℕ)
    (negated : Bool) (values : BinaryValues WorkCount) :
    (emitCellReference stateCount tapeCount negated).effect values =
      Function.update
        (Function.update
          (Function.update
            (Function.update
              (Function.update values Work.temporary₀ 0) Work.temporary₁ 0)
            Work.temporary₂ 0) Work.available (values Work.available + 1))
        Work.reference₀ 0 :=
  emitCellReference_effect_internal stateCount tapeCount negated values

/-- Exact state-wire copy gate emitted by the executable helper. -/
@[simp] theorem emitStateReference_emitted (stateIndex : ℕ)
    (negated : Bool) (values : BinaryValues WorkCount) :
    (emitStateReference stateIndex negated).emitted values =
      CircuitCode.RawGate.encode
        (CircuitCode.RawGate.copy
          (transitionStateRef (values Work.configBase) stateIndex) negated) :=
  emitStateReference_emitted_internal stateIndex negated values

/-- Exact head-wire copy gate emitted by the executable helper. -/
@[simp] theorem emitHeadReference_emitted (stateCount : ℕ)
    (negated : Bool) (values : BinaryValues WorkCount) :
    (emitHeadReference stateCount negated).emitted values =
      CircuitCode.RawGate.encode
        (CircuitCode.RawGate.copy
          (transitionHeadRef stateCount (values Work.horizon)
            (values Work.configBase) (values Work.tapeIndex)
            (values Work.position)) negated) :=
  emitHeadReference_emitted_internal stateCount negated values

/-- Exact cell-symbol wire copy gate emitted by the executable helper. -/
@[simp] theorem emitCellReference_emitted (stateCount tapeCount : ℕ)
    (negated : Bool) (values : BinaryValues WorkCount) :
    (emitCellReference stateCount tapeCount negated).emitted values =
      CircuitCode.RawGate.encode
        (CircuitCode.RawGate.copy
          (transitionCellRef stateCount tapeCount (values Work.horizon)
            (values Work.configBase) (values Work.tapeIndex)
            (values Work.position) (values Work.symbolIndex)) negated) :=
  emitCellReference_emitted_internal stateCount tapeCount negated values

end DirectGenerator

end Serializer

end CircuitUnrolling

end Complexity
