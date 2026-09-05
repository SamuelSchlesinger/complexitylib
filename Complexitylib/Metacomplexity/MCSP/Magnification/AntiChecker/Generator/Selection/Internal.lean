/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.MCSP.Magnification.AntiChecker.Generator.Selection.Defs
import Complexitylib.Circuits.Composition
import Complexitylib.Circuits.InputSources
import Complexitylib.Circuits.KeyedMinimumTournament
import Complexitylib.Circuits.KeyedMinimumTournament.Family
import Complexitylib.Metacomplexity.MCSP
import Complexitylib.Metacomplexity.MCSP.Magnification.AntiChecker.Counter.Encoding

/-!
# Circuit-level anti-checker selection rounds -- proof internals
-/


public section

namespace Complexity

namespace GapMCSP

namespace Magnification

namespace AntiCheckerLemma

theorem eval_candidateCounterInputCircuit_internal
    {arity prefixLength : ℕ} (candidate : Fin (2 ^ arity))
    (table : BitString (2 ^ arity))
    (packedPrefix : BitString (prefixLength * (arity + 1))) :
    (candidateCounterInputCircuit arity prefixLength candidate).eval
        (selectionRoundInput table packedPrefix) =
      packLabeledSamples
        (candidateLabeledSamples candidate table packedPrefix) := by
  rw [candidateCounterInputCircuit, Circuit.eval_inputSources]
  funext coordinate
  generalize hposition : finProdFinEquiv.symm coordinate = position
  have hcoordinate := congrArg finProdFinEquiv hposition
  simp only [Equiv.apply_symm_apply] at hcoordinate
  subst coordinate
  rcases position with ⟨row, cell⟩
  refine Fin.cases ?_ (fun prefixRow => ?_) row
  · refine Fin.lastCases ?_ (fun inputCoordinate => ?_) cell
    · simp [candidateCounterSources, selectionRoundInput,
        candidateLabeledSamples, candidateSample,
        Circuit.InputSource.eval, packLabeledSamples]
    · simp [candidateCounterSources,
        candidateLabeledSamples, candidateSample,
        Circuit.InputSource.eval, packLabeledSamples]
  · refine Fin.lastCases ?_ (fun inputCoordinate => ?_) cell
    · simp [candidateCounterSources, selectionRoundInput,
        candidateLabeledSamples, Circuit.InputSource.eval,
        packLabeledSamples, unpackLabeledSamples,
        unpackLabeledSample]
    · simp [candidateCounterSources, selectionRoundInput,
        candidateLabeledSamples, Circuit.InputSource.eval,
        packLabeledSamples, unpackLabeledSamples,
        unpackLabeledSample]

theorem eval_candidateSampleCircuit_internal
    {arity prefixLength : ℕ} (candidate : Fin (2 ^ arity))
    (table : BitString (2 ^ arity))
    (packedPrefix : BitString (prefixLength * (arity + 1))) :
    (candidateSampleCircuit arity prefixLength candidate).eval
        (selectionRoundInput table packedPrefix) =
      candidateSampleBits candidate table := by
  rw [candidateSampleCircuit, Circuit.eval_inputSources]
  funext coordinate
  refine Fin.lastCases ?_ (fun inputCoordinate => ?_) coordinate
  · simp [candidateSampleSources, selectionRoundInput,
      candidateSampleBits, Circuit.InputSource.eval]
  · simp [candidateSampleSources, candidateSampleBits,
      Circuit.InputSource.eval]

theorem eval_candidateCounterRecordCircuit_internal
    {overhead arity prefixLength : ℕ} {beta : PositiveRationalScale}
    (counter : ApproximateCounterCircuit overhead beta arity prefixLength)
    (candidate : Fin (2 ^ arity)) (table : BitString (2 ^ arity))
    (packedPrefix : BitString (prefixLength * (arity + 1))) :
    (candidateCounterRecordCircuit counter candidate).2.eval
        (selectionRoundInput table packedPrefix) =
      Fin.append
        (counter.circuit.eval
          (packLabeledSamples
            (candidateLabeledSamples candidate table packedPrefix)))
        (candidateSampleBits candidate table) := by
  unfold candidateCounterRecordCircuit
  rw [Circuit.eval_parallel, Circuit.eval_compose,
    eval_candidateCounterInputCircuit_internal,
    eval_candidateSampleCircuit_internal]

theorem size_candidateCounterRecordCircuit_internal
    {overhead arity prefixLength : ℕ} {beta : PositiveRationalScale}
    (counter : ApproximateCounterCircuit overhead beta arity prefixLength)
    (candidate : Fin (2 ^ arity)) :
    (candidateCounterRecordCircuit counter candidate).2.size =
      counter.circuit.size +
        (prefixLength + 1) * (arity + 1) + (arity + 1) := by
  unfold candidateCounterRecordCircuit
  rw [Circuit.size_parallel, Circuit.size_compose,
    candidateCounterInputCircuit, candidateSampleCircuit,
    Circuit.size_inputSources, Circuit.size_inputSources]
  omega

theorem selectionCandidateCount_add_one_internal (arity : ℕ) :
    selectionCandidateCount arity + 1 = 2 ^ arity := by
  exact Nat.sub_add_cancel Nat.one_le_two_pow

theorem eval_packedCandidateCounterRecords_internal
    {overhead arity prefixLength : ℕ} {beta : PositiveRationalScale}
    (counter : ApproximateCounterCircuit overhead beta arity prefixLength)
    (table : BitString (2 ^ arity))
    (packedPrefix : BitString (prefixLength * (arity + 1))) :
    (packedCandidateCounterRecords counter).2.eval
        (selectionRoundInput table packedPrefix) =
      BitString.packKeyedRecords (selectionCandidateCount arity)
        (candidateCounterKeys counter table packedPrefix)
        (candidateCounterPayloads table) := by
  unfold packedCandidateCounterRecords
  apply Circuit.eval_parallelKeyedRecordFamily
  intro index
  simpa only [candidateCounterRecordFamily, candidateCounterKeys,
      candidateCounterPayloads, candidateCounterKey] using
    eval_candidateCounterRecordCircuit_internal counter
      (selectionCandidateEquiv arity index) table packedPrefix

theorem size_packedCandidateCounterRecords_internal
    {overhead arity prefixLength : ℕ} {beta : PositiveRationalScale}
    (counter : ApproximateCounterCircuit overhead beta arity prefixLength) :
    (packedCandidateCounterRecords counter).2.size =
      (selectionCandidateCount arity + 1) *
        (counter.circuit.size +
          (prefixLength + 1) * (arity + 1) + (arity + 1)) := by
  unfold packedCandidateCounterRecords
  rw [Circuit.size_parallelKeyedRecordFamily]
  simp only [candidateCounterRecordFamily]
  simp_rw [size_candidateCounterRecordCircuit_internal]
  simp

theorem eval_minimumCounterRecordCircuit_internal
    {overhead arity prefixLength : ℕ} {beta : PositiveRationalScale}
    (counter : ApproximateCounterCircuit overhead beta arity prefixLength)
    (table : BitString (2 ^ arity))
    (packedPrefix : BitString (prefixLength * (arity + 1))) :
    (minimumCounterRecordCircuit counter).2.eval
        (selectionRoundInput table packedPrefix) =
      Fin.append (minimumCounterRecord counter table packedPrefix).1
        (minimumCounterRecord counter table packedPrefix).2 := by
  unfold minimumCounterRecordCircuit
  rw [Circuit.eval_compose,
    eval_packedCandidateCounterRecords_internal,
    Circuit.eval_unsignedKeyedMinTournament]
  rfl

theorem size_minimumCounterRecordCircuit_internal
    {overhead arity prefixLength : ℕ} {beta : PositiveRationalScale}
    (counter : ApproximateCounterCircuit overhead beta arity prefixLength) :
    (minimumCounterRecordCircuit counter).2.size =
      (selectionCandidateCount arity + 1) *
          (counter.circuit.size +
            (prefixLength + 1) * (arity + 1) + (arity + 1)) +
        ((selectionCandidateCount arity + 1) *
            (counterOutputWidth beta arity + (arity + 1)) +
          selectionCandidateCount arity *
            (20 * counterOutputWidth beta arity +
              5 * (arity + 1) + 1)) := by
  unfold minimumCounterRecordCircuit
  rw [Circuit.size_compose,
    size_packedCandidateCounterRecords_internal,
    Circuit.size_unsignedKeyedMinTournament]

theorem candidateSampleBits_input_internal {arity : ℕ}
    (candidate : Fin (2 ^ arity)) (table : BitString (2 ^ arity))
    (coordinate : Fin arity) :
    candidateSampleBits candidate table coordinate.castSucc =
      MCSP.Instance.inputOfIndex candidate coordinate := by
  simp [candidateSampleBits]

theorem candidateSampleBits_output_internal {arity : ℕ}
    (candidate : Fin (2 ^ arity)) (table : BitString (2 ^ arity)) :
    candidateSampleBits candidate table (Fin.last arity) = table candidate := by
  simp [candidateSampleBits]

theorem exists_minimumCounterRecord_eq_candidate_internal
    {overhead arity prefixLength : ℕ} {beta : PositiveRationalScale}
    (counter : ApproximateCounterCircuit overhead beta arity prefixLength)
    (table : BitString (2 ^ arity))
    (packedPrefix : BitString (prefixLength * (arity + 1))) :
    ∃ candidate : Fin (2 ^ arity),
      minimumCounterRecord counter table packedPrefix =
        (candidateCounterKey counter candidate table packedPrefix,
          candidateSampleBits candidate table) := by
  obtain ⟨index, hindex⟩ :=
    BitString.exists_unsignedMinimumKeyedRecord_eq
      (selectionCandidateCount arity)
      (candidateCounterKeys counter table packedPrefix)
      (candidateCounterPayloads table)
  refine ⟨selectionCandidateEquiv arity index, ?_⟩
  simpa only [minimumCounterRecord, candidateCounterKeys,
    candidateCounterPayloads] using hindex

theorem minimumCounterRecord_key_le_candidate_internal
    {overhead arity prefixLength : ℕ} {beta : PositiveRationalScale}
    (counter : ApproximateCounterCircuit overhead beta arity prefixLength)
    (table : BitString (2 ^ arity))
    (packedPrefix : BitString (prefixLength * (arity + 1)))
    (candidate : Fin (2 ^ arity)) :
    (minimumCounterRecord counter table packedPrefix).1.unsignedValue ≤
      (candidateCounterKey counter candidate table
        packedPrefix).unsignedValue := by
  have hminimum := BitString.unsignedMinimumKeyedRecord_key_le
    (selectionCandidateCount arity)
    (candidateCounterKeys counter table packedPrefix)
    (candidateCounterPayloads table)
    ((selectionCandidateEquiv arity).symm candidate)
  simpa only [minimumCounterRecord, candidateCounterKeys,
    Equiv.apply_symm_apply] using hminimum

theorem exists_minimumCounterRecord_candidate_isEstimateMinimizer_internal
    {overhead arity prefixLength : ℕ} {beta : PositiveRationalScale}
    (counter : ApproximateCounterCircuit overhead beta arity prefixLength)
    (table : BitString (2 ^ arity))
    (packedPrefix : BitString (prefixLength * (arity + 1))) :
    ∃ candidate : Fin (2 ^ arity),
      minimumCounterRecord counter table packedPrefix =
          (candidateCounterKey counter candidate table packedPrefix,
            candidateSampleBits candidate table) ∧
        AntiChecker.IsEstimateMinimizer
          (counterRoundEstimate counter table packedPrefix)
          (MCSP.Instance.inputOfIndex candidate) := by
  obtain ⟨candidate, hrecord⟩ :=
    exists_minimumCounterRecord_eq_candidate_internal
      counter table packedPrefix
  refine ⟨candidate, hrecord, ?_⟩
  intro input
  have hminimum := minimumCounterRecord_key_le_candidate_internal
    counter table packedPrefix (MCSP.Instance.inputIndex input)
  rw [hrecord] at hminimum
  simp only [counterRoundEstimate, ApproximateCounterCircuit.estimate, counterValue,
    MCSP.Instance.inputIndex_inputOfIndex]
  exact hminimum

theorem exists_eval_minimumCounterRecordCircuit_eq_candidate_internal
    {overhead arity prefixLength : ℕ} {beta : PositiveRationalScale}
    (counter : ApproximateCounterCircuit overhead beta arity prefixLength)
    (table : BitString (2 ^ arity))
    (packedPrefix : BitString (prefixLength * (arity + 1))) :
    ∃ candidate : Fin (2 ^ arity),
      (minimumCounterRecordCircuit counter).2.eval
          (selectionRoundInput table packedPrefix) =
        Fin.append
          (candidateCounterKey counter candidate table packedPrefix)
          (candidateSampleBits candidate table) ∧
        AntiChecker.IsEstimateMinimizer
          (counterRoundEstimate counter table packedPrefix)
          (MCSP.Instance.inputOfIndex candidate) := by
  obtain ⟨candidate, hrecord, hminimum⟩ :=
    exists_minimumCounterRecord_candidate_isEstimateMinimizer_internal
      counter table packedPrefix
  refine ⟨candidate, ?_, hminimum⟩
  rw [eval_minimumCounterRecordCircuit_internal, hrecord]

end AntiCheckerLemma

end Magnification

end GapMCSP

end Complexity
