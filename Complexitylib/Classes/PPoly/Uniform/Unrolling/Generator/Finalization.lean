/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Classes.PPoly.Uniform.Unrolling.Generator.Finalization.Defs
public import Complexitylib.Classes.PPoly.Uniform.Unrolling.Generator.Finalization.Internal

/-!
# Direct-unrolling finalization generator

This module exposes the verified acceptance, dead-padding, and terminal-copy
phase of the executable direct-unrolling serializer. Padding is driven by the
binary `available` counter and the precomputed closed frontier, so the routine
uses logarithmic-width work values and performs no preliminary counting pass.
-/

@[expose] public section

namespace Complexity

namespace CircuitUnrolling

namespace Serializer

namespace DirectGenerator

/-- Preparing the two numeric acceptance references is sound. -/
theorem prepareAcceptanceReferences_sound (tm : TM k) :
    (prepareAcceptanceReferences tm).Sound :=
  prepareAcceptanceReferences_sound_internal tm

/-- The arithmetic preparation domain follows from its two reusable zero
counters. -/
theorem prepareAcceptanceReferences_requires (tm : TM k)
    (values : BinaryValues WorkCount)
    (hadd : values Work.addCounter = 0)
    (hmultiply : values Work.multiplyCounter = 0) :
    (prepareAcceptanceReferences tm).requires values :=
  prepareAcceptanceReferences_requires_internal tm values hadd hmultiply

/-- Exact pure endpoint of acceptance-reference preparation. -/
@[simp] theorem prepareAcceptanceReferences_effect (tm : TM k)
    (values : BinaryValues WorkCount) :
    (prepareAcceptanceReferences tm).effect values =
      acceptanceReferenceValues tm values :=
  prepareAcceptanceReferences_effect_internal tm values

/-- Reference preparation emits no code bits. -/
@[simp] theorem prepareAcceptanceReferences_emitted (tm : TM k)
    (values : BinaryValues WorkCount) :
    (prepareAcceptanceReferences tm).emitted values = [] :=
  prepareAcceptanceReferences_emitted_internal tm values

/-- Saving and emitting the original acceptance gate is sound. -/
theorem emitAcceptance_sound (tm : TM k) : (emitAcceptance tm).Sound :=
  emitAcceptance_sound_internal tm

/-- The acceptance phase's reusable-counter domain. -/
theorem emitAcceptance_requires (tm : TM k)
    (values : BinaryValues WorkCount)
    (hemit : values Work.emitCounter = 0)
    (hcopy : values Work.copyCounter = 0)
    (hadd : values Work.addCounter = 0)
    (hmultiply : values Work.multiplyCounter = 0) :
    (emitAcceptance tm).requires values :=
  emitAcceptance_requires_internal tm values hemit hcopy hadd hmultiply

/-- Exact pure endpoint after the original acceptance gate. -/
@[simp] theorem emitAcceptance_effect (tm : TM k)
    (values : BinaryValues WorkCount) :
    (emitAcceptance tm).effect values = afterAcceptanceValues tm values :=
  emitAcceptance_effect_internal tm values

/-- The acceptance phase emits exactly the numeric acceptance gate. -/
@[simp] theorem emitAcceptance_emitted (tm : TM k)
    (values : BinaryValues WorkCount) :
    (emitAcceptance tm).emitted values =
      CircuitCode.RawGate.encode (currentAcceptanceGate tm values) :=
  emitAcceptance_emitted_internal tm values

/-- The dead-gate loop is sound. -/
theorem emitPadding_sound : emitPadding.Sound := emitPadding_sound_internal

/-- The dead-gate loop's controller and emission precondition. -/
theorem emitPadding_requires (values : BinaryValues WorkCount)
    (hle : values Work.available ≤ values Work.frontier)
    (hemit : values Work.emitCounter = 0) :
    emitPadding.requires values :=
  emitPadding_requires_internal values hle hemit

/-- Padding retains a fixed-width pointwise space certificate whenever its
closed frontier and preserved zero reference fit that width. The number of
emitted dead gates does not contribute additively to auxiliary space. -/
theorem emitPadding_spaceBoundByWidth
    {initialSpace : ℕ → ℕ} {values : ℕ → BinaryValues WorkCount}
    {width : ℕ → ℕ}
    (hfrontier : ∀ inputLength,
      values inputLength Work.frontier ≤ width inputLength)
    (hreference : ∀ inputLength,
      values inputLength Work.reference₀ ≤ width inputLength) :
    BinaryRoutine.SpaceBoundByWidthAt emitPadding initialSpace values width :=
  emitPadding_spaceBoundByWidth_internal hfrontier hreference

/-- From a zero reference, padding emits exactly the closed-frontier
shortfall as constant-false raw gates. -/
theorem emitPadding_emitted (values : BinaryValues WorkCount)
    (hzero : values Work.reference₀ = 0) :
    emitPadding.emitted values =
      (List.replicate
        (values Work.frontier - values Work.available)
        (CircuitCode.RawGate.constant 0 false)).flatMap
          CircuitCode.RawGate.encode :=
  emitPadding_emitted_internal values hzero

/-- The terminal acceptance-wire copy is sound. -/
theorem emitTerminalCopy_sound : emitTerminalCopy.Sound :=
  emitTerminalCopy_sound_internal

/-- Exact terminal copy emitted from the saved output reference. -/
@[simp] theorem emitTerminalCopy_emitted (values : BinaryValues WorkCount) :
    emitTerminalCopy.emitted values =
      CircuitCode.RawGate.encode
        (CircuitCode.RawGate.copy (values Work.savedOutput)) :=
  emitTerminalCopy_emitted_internal values

/-- The complete finalization phase is sound. -/
theorem finalization_sound (tm : TM k) : (finalization tm).Sound :=
  finalization_sound_internal tm

/-- Finalization is available whenever all reusable counters are zero and
the acceptance gate still fits below the closed padding frontier. -/
theorem finalization_requires (tm : TM k)
    (values : BinaryValues WorkCount)
    (hemit : values Work.emitCounter = 0)
    (hcopy : values Work.copyCounter = 0)
    (hadd : values Work.addCounter = 0)
    (hmultiply : values Work.multiplyCounter = 0)
    (hle : values Work.available + 1 ≤ values Work.frontier) :
    (finalization tm).requires values :=
  finalization_requires_internal tm values hemit hcopy hadd hmultiply hle

/-- If every incoming work value is bounded by one fixed polynomial, then
the full acceptance, padding, terminal-copy, and cleanup phase has a
pointwise polynomial-width auxiliary-space certificate. -/
theorem finalization_spaceBoundByPolynomial
    (tm : TM k) (p : Polynomial ℕ) {initialSpace : ℕ → ℕ}
    {values : ℕ → BinaryValues WorkCount}
    (hvalues : ∀ inputLength index,
      values inputLength index ≤ p.eval inputLength) :
    ∃ width : Polynomial ℕ,
      BinaryRoutine.SpaceBoundByWidthAt (finalization tm) initialSpace values
        width.eval :=
  finalization_spaceBoundByPolynomial_internal tm p hvalues

/-- Polynomially bounded incoming work values make the complete finalization
phase logarithmic-space, provided the incoming auxiliary-space budget is
already logarithmic. -/
theorem finalization_space_bigO_log
    (tm : TM k) (p : Polynomial ℕ) {initialSpace : ℕ → ℕ}
    {values : ℕ → BinaryValues WorkCount}
    (hinitial : initialSpace =O
      (fun inputLength => Nat.log 2 inputLength))
    (hvalues : ∀ inputLength index,
      values inputLength index ≤ p.eval inputLength) :
    BinaryRoutine.SpaceBoundInLogAt (finalization tm) initialSpace values :=
  finalization_space_bigO_log_internal tm p hinitial hvalues

/-- Exact acceptance, padding, and terminal-copy word from an arbitrary pure
entry vector. -/
theorem finalization_emitted (tm : TM k)
    (values : BinaryValues WorkCount) :
    (finalization tm).emitted values =
      CircuitCode.RawGate.encode (currentAcceptanceGate tm values) ++
        (List.replicate
          (values Work.frontier - (values Work.available + 1))
          (CircuitCode.RawGate.constant 0 false)).flatMap
            CircuitCode.RawGate.encode ++
        CircuitCode.RawGate.encode
          (CircuitCode.RawGate.copy (values Work.available)) :=
  finalization_emitted_internal tm values

/-- Under the numeric tableau endpoint equations, finalization emits exactly
the serializer's acceptance gate and padded suffix. -/
theorem finalization_emitted_eq_numericSchedule (tm : TM k)
    (values : BinaryValues WorkCount) (n originalRawGateCount closedBound T
      finalConfigBase : ℕ)
    (hn : 0 < n)
    (havailable : values Work.available = n + originalRawGateCount - 1)
    (hfrontier : values Work.frontier = n + closedBound)
    (hhorizon : values Work.horizon = T)
    (hconfigBase : values Work.configBase = finalConfigBase) :
    (finalization tm).emitted values =
      ([numericAcceptanceGate (Fintype.card tm.Q)
          (stateIndex tm.toNTM tm.qhalt) (k + 2) T finalConfigBase] ++
        directFinalizationSuffix n originalRawGateCount closedBound).flatMap
          CircuitCode.RawGate.encode :=
  finalization_emitted_eq_numericSchedule_internal tm values n
    originalRawGateCount closedBound T finalConfigBase hn havailable hfrontier
    hhorizon hconfigBase

end DirectGenerator

end Serializer

end CircuitUnrolling

end Complexity
