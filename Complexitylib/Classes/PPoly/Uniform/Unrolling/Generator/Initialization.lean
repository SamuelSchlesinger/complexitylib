/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Classes.PPoly.Uniform.Unrolling.Generator.Initialization.Defs
public import Complexitylib.Classes.PPoly.Uniform.Unrolling.Generator.Initialization.Internal

/-!
# Verified direct-unrolling initialization generator

This module exposes soundness, logarithmic all-prefix space, exact pure
effects, exact raw-gate emission, and the positive-input entry contract for
the direct initialization phase.
-/

@[expose] public section

namespace Complexity

namespace CircuitUnrolling

namespace Serializer

namespace DirectGenerator

theorem emitConstantGate_sound (value : Bool) :
    (emitConstantGate value).Sound :=
  emitConstantGate_sound_internal value

theorem emitCopyGate_sound (reference : Fin WorkCount) (negated : Bool) :
    (emitCopyGate reference negated).Sound :=
  emitCopyGate_sound_internal reference negated

/-- Emitting a constant gate has a pointwise width certificate when the
first-unused-wire frontier and the shared constant reference fit the width. -/
theorem emitConstantGate_spaceBoundByWidth
    (value : Bool) {initialSpace : ℕ → ℕ}
    {values : ℕ → BinaryValues WorkCount} {width : ℕ → ℕ}
    (havailable : ∀ inputLength,
      values inputLength Work.available ≤ width inputLength)
    (hreference : ∀ inputLength,
      values inputLength Work.reference₀ ≤ width inputLength) :
    BinaryRoutine.SpaceBoundByWidthAt (emitConstantGate value)
      initialSpace values width :=
  emitConstantGate_spaceBoundByWidth_internal value havailable hreference

/-- Emitting a copy gate has a pointwise width certificate when the
first-unused-wire frontier and copied reference fit the width. -/
theorem emitCopyGate_spaceBoundByWidth
    (reference : Fin WorkCount) (negated : Bool)
    {initialSpace : ℕ → ℕ} {values : ℕ → BinaryValues WorkCount}
    {width : ℕ → ℕ}
    (havailable : ∀ inputLength,
      values inputLength Work.available ≤ width inputLength)
    (hreference : ∀ inputLength,
      values inputLength reference ≤ width inputLength) :
    BinaryRoutine.SpaceBoundByWidthAt (emitCopyGate reference negated)
      initialSpace values width :=
  emitCopyGate_spaceBoundByWidth_internal reference negated havailable
    hreference

theorem emitStartCell_sound : emitStartCell.Sound :=
  emitStartCell_sound_internal

theorem emitBlankCell_sound : emitBlankCell.Sound :=
  emitBlankCell_sound_internal

theorem emitInputDataCell_sound : emitInputDataCell.Sound :=
  emitInputDataCell_sound_internal

theorem emitInitialStates_sound (tm : TM k) :
    (emitInitialStates tm).Sound :=
  emitInitialStates_sound_internal tm

theorem setHorizonLimit_sound : setHorizonLimit.Sound :=
  setHorizonLimit_sound_internal

theorem setInputLimit_sound : setInputLimit.Sound :=
  setInputLimit_sound_internal

theorem emitHeadPosition_sound : emitHeadPosition.Sound :=
  emitHeadPosition_sound_internal

theorem emitHeadTape_sound : emitHeadTape.Sound :=
  emitHeadTape_sound_internal

theorem emitInputCells_sound : emitInputCells.Sound :=
  emitInputCells_sound_internal

theorem emitBlankTape_sound : emitBlankTape.Sound :=
  emitBlankTape_sound_internal

theorem initialization_sound (tm : TM k) :
    (initialization tm).Sound :=
  initialization_sound_internal tm

/-- Direct initialization uses logarithmic all-prefix space after the positive
polynomial preamble has prepared its numeric work-vector entry state. -/
theorem initialization_space_bigO_log (tm : TM k) (q : Polynomial ℕ) :
    BinaryRoutine.SpaceBoundInLogAt (initialization tm)
      TM.binaryLengthSpace
      (fun inputLength => preambleValues tm q
        (BinaryRoutine.inputLengthValues Work.inputLength inputLength)) :=
  initialization_space_bigO_log_internal tm q

/-- Exact work-vector effect of initialization on its natural value-level
domain. In particular, `loop₀` is restored and `limit₀` is cleared. -/
theorem initialization_effect (tm : TM k)
    (values : BinaryValues WorkCount)
    (hreference : values Work.reference₀ = 0)
    (hloop : values Work.loop₀ = 0)
    (hinput : values Work.inputLength ≤ values Work.horizon + 1) :
    (initialization tm).effect values =
      Function.update
        (Function.update values Work.available
          (values Work.available + Fintype.card tm.Q +
            (values Work.horizon + 1) * (k + 2) + 4 +
            4 * (values Work.horizon + 1) +
            (4 + 4 * (values Work.horizon + 1)) * (k + 1)))
        Work.limit₀ 0 :=
  initialization_effect_internal tm values hreference hloop hinput

/-- Exact encoded raw-gate stream emitted by initialization. -/
theorem initialization_emitted (tm : TM k)
    (values : BinaryValues WorkCount)
    (hreference : values Work.reference₀ = 0)
    (hloop : values Work.loop₀ = 0)
    (hinput : values Work.inputLength ≤ values Work.horizon + 1) :
    (initialization tm).emitted values =
      (directInitSchedule tm (values Work.horizon)
        (values Work.inputLength)).flatMap CircuitCode.RawGate.encode :=
  initialization_emitted_internal tm values hreference hloop hinput

/-- Exact endpoint after the verified positive preamble. -/
theorem initialization_effect_preambleValues
    (tm : TM k) (q : Polynomial ℕ) (n : ℕ) :
    let values := preambleValues tm q
      (BinaryRoutine.inputLengthValues Work.inputLength n)
    let T := (TM.directSerializerHorizonPolynomial q).eval n
    (initialization tm).effect values =
      Function.update
        (Function.update values Work.available
          (n + Fintype.card tm.Q + (T + 1) * (k + 2) + 4 +
            4 * (T + 1) + (4 + 4 * (T + 1)) * (k + 1)))
        Work.limit₀ 0 :=
  initialization_effect_preambleValues_internal tm q n

/-- The positive preamble causes initialization to emit exactly the numeric
direct-initialization schedule at the normalized horizon. -/
@[simp] theorem initialization_emitted_preambleValues
    (tm : TM k) (q : Polynomial ℕ) (n : ℕ) :
    (initialization tm).emitted
        (preambleValues tm q
          (BinaryRoutine.inputLengthValues Work.inputLength n)) =
      (directInitSchedule tm
        ((TM.directSerializerHorizonPolynomial q).eval n) n).flatMap
          CircuitCode.RawGate.encode :=
  initialization_emitted_preambleValues_internal tm q n

@[simp] theorem initialization_loop_restored_preambleValues
    (tm : TM k) (q : Polynomial ℕ) (n : ℕ) :
    (initialization tm).effect
        (preambleValues tm q
          (BinaryRoutine.inputLengthValues Work.inputLength n))
      Work.loop₀ = 0 :=
  initialization_loop_restored_preambleValues_internal tm q n

@[simp] theorem initialization_limit_restored_preambleValues
    (tm : TM k) (q : Polynomial ℕ) (n : ℕ) :
    (initialization tm).effect
        (preambleValues tm q
          (BinaryRoutine.inputLengthValues Work.inputLength n))
      Work.limit₀ = 0 :=
  initialization_limit_restored_preambleValues_internal tm q n

/-- The normalized horizon bound discharges every initialization leaf and
loop obligation at positive-input entry. -/
theorem initialization_requires_preambleValues
    (tm : TM k) (q : Polynomial ℕ) (n : ℕ) (hn : 0 < n) :
    (initialization tm).requires
      (preambleValues tm q
        (BinaryRoutine.inputLengthValues Work.inputLength n)) :=
  initialization_requires_preambleValues_internal tm q n hn

end DirectGenerator

end Serializer

end CircuitUnrolling

end Complexity
