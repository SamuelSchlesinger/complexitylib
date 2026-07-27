/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Classes.PPoly.Uniform.Unrolling.Generator.Transition.Effect.Defs
public import Complexitylib.Classes.PPoly.Uniform.Unrolling.Generator.Transition.Effect.Internal

/-!
# Direct-unrolling transition-effect generator

Exact contracts for the generated disjunction over a machine's finite
transition table.
-/

@[expose] public section

namespace Complexity

namespace CircuitUnrolling

namespace Serializer

namespace DirectGenerator

/-- Complete transition-effect emission is sound. -/
theorem emitEffectFormula_sound (tm : NTM k)
    (selects : TransitionEffect tm → Bool) :
    (emitEffectFormula tm selects).Sound :=
  emitEffectFormula_sound_internal tm selects

/-- Complete transition-effect emission has an all-prefix width certificate
under one global bounded-selector envelope. The cap covers the complete wire
frontier together with every state, head, cell, and read-size intermediate
that any machine-selected case can use. -/
theorem emitEffectFormula_spaceBoundByWidth
    (tm : NTM k) (selects : TransitionEffect tm → Bool)
    {initialSpace : ℕ → ℕ}
    {values : ℕ → BinaryValues WorkCount} {width : ℕ → ℕ}
    (hclean : ∀ inputLength, CaseFormulaClean (values inputLength))
    (hvalues : ∀ inputLength index,
      values inputLength index ≤ width inputLength)
    (hcap : ∀ inputLength stateIndex tapeIndex symbolIndex position,
      stateIndex < Fintype.card tm.Q → tapeIndex ≤ k + 1 →
      symbolIndex < 4 →
      position ≤ values inputLength Work.horizon →
        values inputLength Work.available +
            effectFormulaScheduleSize (transitionCases tm).length k
              (values inputLength Work.horizon)
              (effectCaseSelectedAt tm selects) (effectCaseChoiceAt tm) +
          transitionStateRef (values inputLength Work.configBase)
            stateIndex +
          (transitionHeadRef (Fintype.card tm.Q)
                (values inputLength Work.horizon)
                (values inputLength Work.configBase) tapeIndex position +
              tapeIndex + values inputLength Work.horizon + 1) +
          (transitionCellRef (Fintype.card tm.Q) (k + 2)
                (values inputLength Work.horizon)
                (values inputLength Work.configBase) tapeIndex position
                symbolIndex +
              (tapeIndex * (values inputLength Work.horizon + 2) +
                position) +
              (values inputLength Work.horizon + 2) + (k + 2) +
              tapeIndex + 4) +
          caseReadSize (values inputLength Work.horizon) +
          values inputLength Work.horizon ≤ width inputLength) :
    BinaryRoutine.SpaceBoundByWidthAt (emitEffectFormula tm selects)
      initialSpace values width :=
  emitEffectFormula_spaceBoundByWidth_internal tm selects hclean hvalues hcap

/-- Clean scratch together with a positive wire frontier suffices for every
leaf routine in complete transition-effect emission. -/
theorem emitEffectFormula_requires (tm : NTM k)
    (selects : TransitionEffect tm → Bool)
    (values : BinaryValues WorkCount) (hclean : CaseFormulaClean values)
    (havailable : 1 ≤ values Work.available) :
    (emitEffectFormula tm selects).requires values :=
  emitEffectFormula_requires_internal tm selects values hclean havailable

/-- Complete transition-effect emission restores all owned scratch and
advances only the wire frontier by the exact numeric schedule size. -/
@[simp] theorem emitEffectFormula_effect (tm : NTM k)
    (selects : TransitionEffect tm → Bool)
    (values : BinaryValues WorkCount) (hclean : CaseFormulaClean values)
    (havailable : 1 ≤ values Work.available) :
    (emitEffectFormula tm selects).effect values =
      Function.update values Work.available
        (values Work.available +
          effectFormulaScheduleSize (transitionCases tm).length k
            (values Work.horizon) (effectCaseSelectedAt tm selects)
            (effectCaseChoiceAt tm)) :=
  emitEffectFormula_effect_internal tm selects values hclean havailable

/-- Complete transition-effect emission is literally the canonical numeric
raw-gate schedule, including its false identity and reverse connector suffix. -/
@[simp] theorem emitEffectFormula_emitted (tm : NTM k)
    (selects : TransitionEffect tm → Bool)
    (values : BinaryValues WorkCount) (hclean : CaseFormulaClean values)
    (havailable : 1 ≤ values Work.available) :
    (emitEffectFormula tm selects).emitted values =
      (effectFormulaSchedule (transitionCases tm).length
        (Fintype.card tm.Q) k (values Work.horizon)
        (values Work.configBase) (values Work.reference₀)
        (values Work.available) (effectCaseSelectedAt tm selects)
        (effectCaseChoiceAt tm) (effectCaseStateIndexAt tm)
        (effectCaseInputSymbolIndexAt tm) (effectCaseOutputSymbolIndexAt tm)
        (effectCaseWorkSymbolIndexAt tm)).flatMap
          CircuitCode.RawGate.encode :=
  emitEffectFormula_emitted_internal tm selects values hclean havailable

end DirectGenerator

end Serializer

end CircuitUnrolling

end Complexity
