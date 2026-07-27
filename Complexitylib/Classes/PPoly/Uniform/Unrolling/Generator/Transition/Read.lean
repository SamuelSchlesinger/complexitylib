/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Classes.PPoly.Uniform.Unrolling.Generator.Transition.Read.Defs
public import Complexitylib.Classes.PPoly.Uniform.Unrolling.Generator.Transition.Read.Internal

/-!
# Direct-unrolling read-formula generator

A stack-free proof-carrying routine that emits the exact numeric gate schedule
for reading one symbol from a bounded encoded configuration.
-/

@[expose] public section

namespace Complexity

namespace CircuitUnrolling

namespace Serializer

namespace DirectGenerator

/-- Complete read-formula emission is sound. -/
theorem emitReadFormula_sound (stateCount tapeCount : ℕ) :
    (emitReadFormula stateCount tapeCount).Sound :=
  emitReadFormula_sound_internal stateCount tapeCount

/-- One reverse-fold connector has a pointwise width certificate when its
frontier and both reference registers fit the shared width. -/
theorem emitReadConnector_spaceBoundByWidth
    {initialSpace : ℕ → ℕ} {values : ℕ → BinaryValues WorkCount}
    {width : ℕ → ℕ}
    (havailable : ∀ inputLength,
      values inputLength Work.available ≤ width inputLength)
    (havailablePositive : ∀ inputLength,
      1 ≤ values inputLength Work.available)
    (hreference₀ : ∀ inputLength,
      values inputLength Work.reference₀ ≤ width inputLength)
    (hreference₁ : ∀ inputLength,
      values inputLength Work.reference₁ ≤ width inputLength) :
    BinaryRoutine.SpaceBoundByWidthAt emitReadConnector initialSpace values
      width :=
  emitReadConnector_spaceBoundByWidth_internal havailable havailablePositive
    hreference₀ hreference₁

/-- Complete read-formula emission has a pointwise width certificate when the
wire frontier and every head- and cell-reference intermediate fit the shared
width. -/
theorem emitReadFormula_spaceBoundByWidth
    (stateCount tapeCount : ℕ) {initialSpace : ℕ → ℕ}
    {values : ℕ → BinaryValues WorkCount} {width : ℕ → ℕ}
    (hclean : ∀ inputLength, ReadFormulaClean (values inputLength))
    (hvalues : ∀ inputLength index,
      values inputLength index ≤ width inputLength)
    (hfrontier : ∀ inputLength,
      values inputLength Work.available +
          (4 * (values inputLength Work.horizon + 1) + 1) ≤
        width inputLength)
    (hheadCap : ∀ inputLength position,
      position ≤ values inputLength Work.horizon →
      transitionHeadRef stateCount (values inputLength Work.horizon)
            (values inputLength Work.configBase)
            (values inputLength Work.tapeIndex) position +
          values inputLength Work.tapeIndex +
          values inputLength Work.horizon + 1 ≤
        width inputLength)
    (hcellCap : ∀ inputLength position,
      position ≤ values inputLength Work.horizon →
      transitionCellRef stateCount tapeCount
            (values inputLength Work.horizon)
            (values inputLength Work.configBase)
            (values inputLength Work.tapeIndex) position
            (values inputLength Work.symbolIndex) +
          (values inputLength Work.tapeIndex *
                (values inputLength Work.horizon + 2) + position) +
          (values inputLength Work.horizon + 2) + tapeCount +
          values inputLength Work.tapeIndex + 4 ≤
        width inputLength) :
    BinaryRoutine.SpaceBoundByWidthAt
      (emitReadFormula stateCount tapeCount) initialSpace values width :=
  emitReadFormula_spaceBoundByWidth_internal stateCount tapeCount hclean
    hvalues hfrontier hheadCap hcellCap

/-- The clean-entry contract suffices for every arithmetic, loop, reference,
and raw-gate leaf in complete read-formula emission. -/
theorem emitReadFormula_requires (stateCount tapeCount : ℕ)
    (values : BinaryValues WorkCount)
    (hclean : ReadFormulaClean values) :
    (emitReadFormula stateCount tapeCount).requires values :=
  emitReadFormula_requires_internal stateCount tapeCount values hclean

/-- Complete read-formula emission restores all owned scratch and only advances
the wire frontier, by four gates per possible head position plus the false
identity gate. -/
@[simp] theorem emitReadFormula_effect (stateCount tapeCount : ℕ)
    (values : BinaryValues WorkCount)
    (hclean : ReadFormulaClean values) :
    (emitReadFormula stateCount tapeCount).effect values =
      Function.update values Work.available
        (values Work.available + (4 * (values Work.horizon + 1) + 1)) :=
  emitReadFormula_effect_internal stateCount tapeCount values hclean

/-- Complete read-formula emission produces exactly the canonical serialized
read-formula schedule at the current horizon and wire frontier. -/
@[simp] theorem emitReadFormula_emitted (stateCount tapeCount : ℕ)
    (values : BinaryValues WorkCount)
    (hclean : ReadFormulaClean values) :
    (emitReadFormula stateCount tapeCount).emitted values =
      (readFormulaSchedule stateCount tapeCount (values Work.horizon)
        (values Work.configBase) (values Work.available)
        (values Work.tapeIndex) (values Work.symbolIndex)).flatMap
          CircuitCode.RawGate.encode :=
  emitReadFormula_emitted_internal stateCount tapeCount values hclean

end DirectGenerator

end Serializer

end CircuitUnrolling

end Complexity
