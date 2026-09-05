/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.MCSP.Magnification.AntiChecker.Generator.Round.Defs
import Complexitylib.Circuits.Composition
import Complexitylib.Circuits.InputProjection
import Complexitylib.Metacomplexity.MCSP.Magnification.AntiChecker.Counter.Encoding
import Complexitylib.Metacomplexity.MCSP.Magnification.AntiChecker.Generator.Selection

/-!
# Iterable anti-checker selection rounds -- proof internals
-/


public section

namespace Complexity

namespace GapMCSP

namespace Magnification

namespace AntiCheckerLemma

private theorem selectionRoundSuccessorInputMap_table
    (beta : PositiveRationalScale) (arity prefixLength : ℕ)
    (tableCoordinate : Fin (2 ^ arity)) :
    selectionRoundSuccessorInputMap beta arity prefixLength
        (Fin.castAdd ((prefixLength + 1) * (arity + 1))
          tableCoordinate) =
      Fin.castAdd (counterOutputWidth beta arity + (arity + 1))
        (Fin.castAdd (prefixLength * (arity + 1)) tableCoordinate) := by
  apply Fin.ext
  simp only [selectionRoundSuccessorInputMap]
  erw [Fin.addCases_left]
  rfl

private theorem selectionRoundSuccessorInputMap_head
    (beta : PositiveRationalScale) (arity prefixLength : ℕ)
    (coordinate : Fin (arity + 1)) :
    selectionRoundSuccessorInputMap beta arity prefixLength
        (Fin.natAdd (2 ^ arity)
          (finProdFinEquiv (0, coordinate))) =
      Fin.natAdd (selectionRoundInputWidth arity prefixLength)
        (Fin.natAdd (counterOutputWidth beta arity) coordinate) := by
  apply Fin.ext
  simp only [selectionRoundSuccessorInputMap]
  erw [Fin.addCases_right]
  simp [selectionRoundInputWidth, Equiv.symm_apply_apply]
  omega

private theorem selectionRoundSuccessorInputMap_tail
    (beta : PositiveRationalScale) (arity prefixLength : ℕ)
    (prefixRow : Fin prefixLength) (coordinate : Fin (arity + 1)) :
    selectionRoundSuccessorInputMap beta arity prefixLength
        (Fin.natAdd (2 ^ arity)
          (finProdFinEquiv (prefixRow.succ, coordinate))) =
      Fin.castAdd (counterOutputWidth beta arity + (arity + 1))
        (Fin.natAdd (2 ^ arity)
          (finProdFinEquiv (prefixRow, coordinate))) := by
  apply Fin.ext
  simp only [selectionRoundSuccessorInputMap]
  erw [Fin.addCases_right]
  simp [Equiv.symm_apply_apply]

private theorem selectionRoundCombinedInput_payload
    {arity prefixLength keyWidth payloadWidth : ℕ}
    (table : BitString (2 ^ arity))
    (packedPrefix : BitString (prefixLength * (arity + 1)))
    (key : BitString keyWidth) (payload : BitString payloadWidth)
    (coordinate : Fin payloadWidth) :
    Fin.append (selectionRoundInput table packedPrefix)
          (Fin.append key payload)
        (Fin.natAdd (selectionRoundInputWidth arity prefixLength)
          (Fin.natAdd keyWidth coordinate)) =
      payload coordinate := by
  simp

theorem selectionRoundSuccessorInputMap_precompose_internal
    {arity prefixLength : ℕ}
    (beta : PositiveRationalScale)
    (candidate : Fin (2 ^ arity)) (table : BitString (2 ^ arity))
    (packedPrefix : BitString (prefixLength * (arity + 1)))
    (key : BitString (counterOutputWidth beta arity)) :
    Fin.append (selectionRoundInput table packedPrefix)
          (Fin.append key (candidateSampleBits candidate table)) ∘
        selectionRoundSuccessorInputMap beta arity prefixLength =
      selectionRoundSuccessorInput candidate table packedPrefix := by
  funext output
  simp only [Function.comp_apply]
  refine Fin.addCases ?_ ?_ output
  · intro tableCoordinate
    rw [selectionRoundSuccessorInputMap_table]
    simp [selectionRoundSuccessorInput, selectionRoundInput,
      selectionRoundInputWidth]
  · intro packedCoordinate
    generalize hposition : finProdFinEquiv.symm packedCoordinate = position
    have hcoordinate := congrArg finProdFinEquiv hposition
    simp only [Equiv.apply_symm_apply] at hcoordinate
    subst packedCoordinate
    rcases position with ⟨row, cell⟩
    refine Fin.cases ?_ (fun prefixRow => ?_) row
    · refine Fin.lastCases ?_ (fun inputCoordinate => ?_) cell
      · rw [selectionRoundSuccessorInputMap_head]
        rw [selectionRoundCombinedInput_payload]
        simp [selectionRoundSuccessorInput, selectionRoundInput,
          candidateLabeledSamples, candidateSample]
      · rw [selectionRoundSuccessorInputMap_head]
        rw [selectionRoundCombinedInput_payload]
        simp [selectionRoundSuccessorInput, selectionRoundInput,
          candidateLabeledSamples, candidateSample]
    · refine Fin.lastCases ?_ (fun inputCoordinate => ?_) cell
      · rw [selectionRoundSuccessorInputMap_tail]
        simp [selectionRoundSuccessorInput, selectionRoundInput,
          selectionRoundInputWidth, candidateLabeledSamples,
          unpackLabeledSamples, unpackLabeledSample]
      · rw [selectionRoundSuccessorInputMap_tail]
        simp [selectionRoundSuccessorInput, selectionRoundInput,
          selectionRoundInputWidth, candidateLabeledSamples,
          unpackLabeledSamples, unpackLabeledSample]

theorem eval_selectionRoundCombinedCircuit_internal
    {overhead arity prefixLength : ℕ} {beta : PositiveRationalScale}
    (counter : ApproximateCounterCircuit overhead beta arity prefixLength)
    (table : BitString (2 ^ arity))
    (packedPrefix : BitString (prefixLength * (arity + 1))) :
    (selectionRoundCombinedCircuit counter).2.eval
        (selectionRoundInput table packedPrefix) =
      Fin.append (selectionRoundInput table packedPrefix)
        ((minimumCounterRecordCircuit counter).2.eval
          (selectionRoundInput table packedPrefix)) := by
  unfold selectionRoundCombinedCircuit
  rw [Circuit.eval_parallel, Circuit.eval_projectInputs]
  rfl

theorem size_selectionRoundCombinedCircuit_internal
    {overhead arity prefixLength : ℕ} {beta : PositiveRationalScale}
    (counter : ApproximateCounterCircuit overhead beta arity prefixLength) :
    (selectionRoundCombinedCircuit counter).2.size =
      selectionRoundInputWidth arity prefixLength +
        (minimumCounterRecordCircuit counter).2.size := by
  unfold selectionRoundCombinedCircuit
  rw [Circuit.size_parallel, Circuit.size_projectInputs]

theorem exists_eval_selectionRoundStateCircuit_eq_successor_internal
    {overhead arity prefixLength : ℕ} {beta : PositiveRationalScale}
    (counter : ApproximateCounterCircuit overhead beta arity prefixLength)
    (table : BitString (2 ^ arity))
    (packedPrefix : BitString (prefixLength * (arity + 1))) :
    ∃ candidate : Fin (2 ^ arity),
      (selectionRoundStateCircuit counter).2.eval
          (selectionRoundInput table packedPrefix) =
          selectionRoundSuccessorInput candidate table packedPrefix ∧
        AntiChecker.IsEstimateMinimizer
          (counterRoundEstimate counter table packedPrefix)
          (MCSP.Instance.inputOfIndex candidate) := by
  obtain ⟨candidate, hminimum, hminimizer⟩ :=
    exists_eval_minimumCounterRecordCircuit_eq_candidate
      counter table packedPrefix
  refine ⟨candidate, ?_, hminimizer⟩
  unfold selectionRoundStateCircuit
  rw [Circuit.eval_compose, Circuit.eval_projectInputs,
    eval_selectionRoundCombinedCircuit_internal, hminimum]
  exact selectionRoundSuccessorInputMap_precompose_internal beta
    candidate table packedPrefix
      (candidateCounterKey counter candidate table packedPrefix)

theorem size_selectionRoundStateCircuit_internal
    {overhead arity prefixLength : ℕ} {beta : PositiveRationalScale}
    (counter : ApproximateCounterCircuit overhead beta arity prefixLength) :
    (selectionRoundStateCircuit counter).2.size =
      selectionRoundInputWidth arity prefixLength +
        (minimumCounterRecordCircuit counter).2.size +
          selectionRoundInputWidth arity (prefixLength + 1) := by
  unfold selectionRoundStateCircuit
  rw [Circuit.size_compose, Circuit.size_projectInputs,
    size_selectionRoundCombinedCircuit_internal]

end AntiCheckerLemma

end Magnification

end GapMCSP

end Complexity
