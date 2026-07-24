/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Models.TuringMachine.OutputProbeDecodeNat.Defs
import Complexitylib.Models.TuringMachine.OutputProbeDecodeTag.Defs
import Complexitylib.Models.TuringMachine.Subroutines.ClearWork.Defs

/-!
# Shared formula-token decoder layout -- definitions

The complete token controller shares its source cursor and query scratch
between fixed-width tag probing and terminated-unary variable decoding. Nine
distinct logical roles make that sharing explicit while keeping all mutable
registers structurally non-aliasing.
-/

namespace Complexity

namespace TM

/-- Nine distinct controller registers used by complete token decoding.

The role order is cursor, query scratch, three retained tag bits, unary value,
unary active flag, loop counter, and fuel. -/
structure OutputProbeDecodeTokenLayout (controllerTapes : ℕ) where
  /-- Injective assignment of logical roles to controller tapes. -/
  roles : Fin 9 ↪ Fin controllerTapes

/-- Restrict a complete token layout to the five fixed-tag roles. -/
def OutputProbeDecodeTokenLayout.tagLayout
    (layout : OutputProbeDecodeTokenLayout controllerTapes) :
    OutputProbeDecodeTagLayout controllerTapes where
  roles :=
    { toFun := fun i => layout.roles ⟨i.val, by omega⟩
      inj' := by
        intro i j hij
        have hroles := layout.roles.injective hij
        apply Fin.ext
        simpa using congrArg Fin.val hroles }

/-- Restrict a complete token layout to the six terminated-unary roles.

Roles zero and one share the tag cursor and scratch. Unary roles two through
five use complete-layout roles five through eight. -/
def OutputProbeDecodeTokenLayout.natLayout
    (layout : OutputProbeDecodeTokenLayout controllerTapes) :
    OutputProbeDecodeNatLayout controllerTapes where
  roles :=
    { toFun := fun i => layout.roles
        ⟨if i.val < 2 then i.val else i.val + 3, by
          by_cases hi : i.val < 2
          · simp [hi]
            omega
          · simp [hi]
            omega⟩
      inj' := by
        intro i j hij
        have hroles := congrArg Fin.val (layout.roles.injective hij)
        apply Fin.ext
        by_cases hi : i.val < 2 <;> by_cases hj : j.val < 2 <;>
          simp [hi, hj] at hroles <;> omega }

/-- Canonical controller frame after clearing all three retained tag bits. -/
def outputProbeDecodeTokenClearedTagExtras (n : ℕ)
    {controllerTapes : ℕ}
    (layout : OutputProbeDecodeTokenLayout controllerTapes)
    (outerExtras : Fin (0 + outputProbeControllerTapes n +
      controllerTapes) → Tape) :
    Fin (0 + outputProbeControllerTapes n + controllerTapes) → Tape :=
  Function.update
    (Function.update
      (Function.update outerExtras
        (outputProbeDecodeTagBitIdx n layout.tagLayout.tag₀Idx)
        (outputProbeCounterTape 0))
      (outputProbeDecodeTagBitIdx n layout.tagLayout.tag₁Idx)
      (outputProbeCounterTape 0))
    (outputProbeDecodeTagBitIdx n layout.tagLayout.tag₂Idx)
    (outputProbeCounterTape 0)

/-- Clear and rewind the three retained tag-bit registers in source order. -/
def outputProbeDecodeTokenClearTagsTM (n controllerTapes : ℕ)
    (layout : OutputProbeDecodeTokenLayout controllerTapes) :
    TM (0 + outputProbeControllerTapes n + controllerTapes) :=
  seqTM
    (clearWorkTM
      (outputProbeDecodeTagBitIdx n layout.tagLayout.tag₀Idx))
    (seqTM
      (clearWorkTM
        (outputProbeDecodeTagBitIdx n layout.tagLayout.tag₁Idx))
      (clearWorkTM
        (outputProbeDecodeTagBitIdx n layout.tagLayout.tag₂Idx)))

/-- Exact time to clear a canonical retained three-bit tag frame. -/
def outputProbeDecodeTokenClearTagsTime (tag₀ tag₁ tag₂ : Bool) : ℕ :=
  clearWorkTimeBound (if tag₀ then 1 else 0).bits.length + 1 +
    (clearWorkTimeBound (if tag₁ then 1 else 0).bits.length + 1 +
      clearWorkTimeBound (if tag₂ then 1 else 0).bits.length)

/-- Dispatch a retained tag after wrapping every selected continuation in the
same three-register cleanup phase. -/
def outputProbeDecodeTokenDispatchTM (n controllerTapes : ℕ)
    (layout : OutputProbeDecodeTokenLayout controllerTapes)
    (onVar onTru onFls onNeg onConj onDisj onInvalid :
      TM (0 + outputProbeControllerTapes n + controllerTapes)) :
    TM (0 + outputProbeControllerTapes n + controllerTapes) :=
  let clearTags := outputProbeDecodeTokenClearTagsTM n controllerTapes layout
  outputProbeDecodeTagDispatchTM n controllerTapes layout.tagLayout
    (seqTM clearTags onVar) (seqTM clearTags onTru)
    (seqTM clearTags onFls) (seqTM clearTags onNeg)
    (seqTM clearTags onConj) (seqTM clearTags onDisj)
    (seqTM clearTags onInvalid)

/-- Exact selected runtime of invariant-restoring token dispatch. -/
def outputProbeDecodeTokenDispatchTime (tag₀ tag₁ tag₂ : Bool)
    (varTime truTime flsTime negTime conjTime disjTime invalidTime : ℕ) :
    ℕ :=
  let clearTime := outputProbeDecodeTokenClearTagsTime tag₀ tag₁ tag₂
  outputProbeDecodeTagDispatchTime tag₀ tag₁ tag₂
    (clearTime + 1 + varTime) (clearTime + 1 + truTime)
    (clearTime + 1 + flsTime) (clearTime + 1 + negTime)
    (clearTime + 1 + conjTime) (clearTime + 1 + disjTime)
    (clearTime + 1 + invalidTime)

/-- Exact cleanup and branch cost when only the selected continuation's
runtime is relevant. -/
def outputProbeDecodeTokenSelectedDispatchTime (tag₀ tag₁ tag₂ : Bool)
    (selectedTime : ℕ) : ℕ :=
  outputProbeDecodeTokenClearTagsTime tag₀ tag₁ tag₂ + 1 + selectedTime +
    outputProbeDecodeTagDispatchDepth tag₀ tag₁

/-- Probe a complete fixed-width tag and dispatch from a normalized token
frame to its selected continuation. -/
def outputProbeDecodeTokenTM (tm : TM n) (controllerTapes : ℕ)
    (layout : OutputProbeDecodeTokenLayout controllerTapes)
    (onVar onTru onFls onNeg onConj onDisj onInvalid :
      TM (0 + outputProbeControllerTapes n + controllerTapes)) :
    TM (0 + outputProbeControllerTapes n + controllerTapes) :=
  seqTM (outputProbeDecodeTagTM tm controllerTapes layout.tagLayout)
    (outputProbeDecodeTokenDispatchTM n controllerTapes layout onVar onTru
      onFls onNeg onConj onDisj onInvalid)

/-- Canonical normalized controller frame after retaining and then clearing a
complete fixed-width tag. The cursor remains advanced by three. -/
def outputProbeDecodeTokenOuterExtrasAfter (n : ℕ)
    {controllerTapes : ℕ}
    (layout : OutputProbeDecodeTokenLayout controllerTapes)
    (outerExtras : Fin (0 + outputProbeControllerTapes n +
      controllerTapes) → Tape)
    (cursor : ℕ) (tag₀ tag₁ tag₂ : Bool) :
    Fin (0 + outputProbeControllerTapes n + controllerTapes) → Tape :=
  outputProbeDecodeTokenClearedTagExtras n layout
    (outputProbeDecodeTagOuterExtrasAfter n layout.tagLayout outerExtras
      cursor tag₀ tag₁ tag₂)

/-- Pure terminated-unary decoder state selected after consuming a complete
three-bit variable tag. -/
def outputProbeDecodeTokenVarInitial (cursor : ℕ) :
    OutputProbeDecodeNatState :=
  { cursor := cursor + 3, value := 0, active := true }

/-- Complete token controller with the variable branch instantiated by the
bounded terminated-unary decoder from the shared layout. -/
def outputProbeDecodeTokenWithNatTM (tm : TM n) (controllerTapes : ℕ)
    (layout : OutputProbeDecodeTokenLayout controllerTapes)
    (onTru onFls onNeg onConj onDisj onInvalid :
      TM (0 + outputProbeControllerTapes n + controllerTapes)) :
    TM (0 + outputProbeControllerTapes n + controllerTapes) :=
  outputProbeDecodeTokenTM tm controllerTapes layout
    (outputProbeDecodeNatTM tm controllerTapes layout.natLayout.cursorIdx
      layout.natLayout.scratchIdx layout.natLayout.valueIdx
      layout.natLayout.activeIdx layout.natLayout.loopIdx
      layout.natLayout.fuelIdx)
    onTru onFls onNeg onConj onDisj onInvalid

end TM

end Complexity
