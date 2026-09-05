/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.MCSP.Magnification.AntiChecker.Generator.Iteration.Defs
import Complexitylib.Circuits.Composition
import Complexitylib.Circuits.InputProjection
import Complexitylib.Metacomplexity.MCSP
import Complexitylib.Metacomplexity.MCSP.Magnification.AntiChecker.Counter.Encoding
import Complexitylib.Metacomplexity.MCSP.Magnification.AntiChecker.Counter.Estimator
import Complexitylib.Metacomplexity.MCSP.Magnification.AntiChecker.Generator.Internal
import Complexitylib.Metacomplexity.MCSP.Magnification.AntiChecker.Generator.Round

/-!
# Finite iteration of anti-checker selection rounds -- proof internals
-/


public section

namespace Complexity

namespace GapMCSP

namespace Magnification

namespace AntiCheckerLemma

theorem eval_selectionPrefixCircuit_zero_internal
    {overhead arity : ℕ} {beta : PositiveRationalScale}
    (family : ApproximateCounterFamily overhead beta arity)
    (hrounds : 0 ≤ requiredRoundCount beta arity)
    (table : BitString (2 ^ arity)) :
    (selectionPrefixCircuit family 0 hrounds).2.eval table =
      selectionRoundInput table (emptyLabeledPrefix arity) := by
  simp only [selectionPrefixCircuit]
  rw [Circuit.eval_projectInputs]
  funext coordinate
  change table (selectionEmptyStateInputMap arity coordinate) =
    Fin.append table (emptyLabeledPrefix arity) coordinate
  have hcoordinate : coordinate =
      Fin.castAdd (0 * (arity + 1))
        (selectionEmptyStateInputMap arity coordinate) := by
    apply Fin.ext
    rfl
  rw [hcoordinate, Fin.append_left]
  apply congrArg table
  apply Fin.ext
  rfl

theorem size_selectionPrefixCircuit_zero_internal
    {overhead arity : ℕ} {beta : PositiveRationalScale}
    (family : ApproximateCounterFamily overhead beta arity)
    (hrounds : 0 ≤ requiredRoundCount beta arity) :
    (selectionPrefixCircuit family 0 hrounds).2.size = 2 ^ arity := by
  simp only [selectionPrefixCircuit]
  rw [Circuit.size_projectInputs]
  simp [selectionRoundInputWidth]

theorem eval_selectionPrefixCircuit_succ_internal
    {overhead arity rounds : ℕ} {beta : PositiveRationalScale}
    (family : ApproximateCounterFamily overhead beta arity)
    (hrounds : rounds + 1 ≤ requiredRoundCount beta arity)
    (table : BitString (2 ^ arity)) :
    (selectionPrefixCircuit family (rounds + 1) hrounds).2.eval table =
      (selectionRoundStateCircuit
        (family.counter (selectionPrefixCounterIndex hrounds))).2.eval
          ((selectionPrefixCircuit family rounds
            (selectionPrefixPriorBound hrounds)).2.eval table) := by
  simp only [selectionPrefixCircuit]
  exact Circuit.eval_compose
    (selectionRoundStateCircuit
      (family.counter (selectionPrefixCounterIndex hrounds))).2
    (selectionPrefixCircuit family rounds
      (selectionPrefixPriorBound hrounds)).2 table

theorem size_selectionPrefixCircuit_succ_internal
    {overhead arity rounds : ℕ} {beta : PositiveRationalScale}
    (family : ApproximateCounterFamily overhead beta arity)
    (hrounds : rounds + 1 ≤ requiredRoundCount beta arity) :
    (selectionPrefixCircuit family (rounds + 1) hrounds).2.size =
      (selectionPrefixCircuit family rounds
          (selectionPrefixPriorBound hrounds)).2.size +
        (selectionRoundStateCircuit
          (family.counter (selectionPrefixCounterIndex hrounds))).2.size := by
  simp only [selectionPrefixCircuit]
  exact Circuit.size_compose
    (selectionRoundStateCircuit
      (family.counter (selectionPrefixCounterIndex hrounds))).2
    (selectionPrefixCircuit family rounds
      (selectionPrefixPriorBound hrounds)).2

theorem candidateLabeledSamples_truthTable_packTargetSamples_internal
    {arity prefixLength : ℕ} (target : BitString arity → Bool)
    (inputs : Fin prefixLength → BitString arity)
    (input : BitString arity) :
    candidateLabeledSamples (MCSP.Instance.inputIndex input)
        (truthTable target) (packTargetSamples target inputs) =
      fun sample =>
        SuccinctMCSP.Sample.ofFunction target
          ((Fin.cons input inputs :
            Fin (prefixLength + 1) → BitString arity) sample) := by
  funext sample
  refine Fin.cases ?_ (fun previous => ?_) sample
  · simp [candidateLabeledSamples, candidateSample,
      SuccinctMCSP.Sample.ofFunction, truthTable_inputIndex_internal]
  · simp [candidateLabeledSamples, packTargetSamples]

theorem selectionRoundSuccessorInput_truthTable_packTargetSamples_internal
    {arity prefixLength : ℕ} (target : BitString arity → Bool)
    (inputs : Fin prefixLength → BitString arity)
    (candidate : Fin (2 ^ arity)) :
    selectionRoundSuccessorInput candidate (truthTable target)
        (packTargetSamples target inputs) =
      selectionTraceState target
        (Fin.cons (MCSP.Instance.inputOfIndex candidate) inputs) := by
  unfold selectionRoundSuccessorInput selectionTraceState
  apply congrArg (selectionRoundInput (truthTable target))
  unfold packTargetSamples
  apply congrArg packLabeledSamples
  have hsamples :=
    candidateLabeledSamples_truthTable_packTargetSamples_internal
      target inputs (MCSP.Instance.inputOfIndex candidate)
  simpa [packTargetSamples] using hsamples

theorem counterRoundEstimate_truthTable_packTargetSamples_internal
    {overhead arity prefixLength : ℕ} {beta : PositiveRationalScale}
    (counter : ApproximateCounterCircuit overhead beta arity prefixLength)
    (target : BitString arity → Bool)
    (inputs : Fin prefixLength → BitString arity)
    (input : BitString arity) :
    counterRoundEstimate counter (truthTable target)
        (packTargetSamples target inputs) input =
      counter.estimate (packTargetSamples target (Fin.cons input inputs)) := by
  unfold counterRoundEstimate
  apply congrArg counter.estimate
  unfold packTargetSamples
  apply congrArg packLabeledSamples
  simpa [packTargetSamples] using
    candidateLabeledSamples_truthTable_packTargetSamples_internal
      target inputs input

private theorem finCons_heq_get_cons_ofFn
    {count : ℕ} {alpha : Type} (head : alpha)
    (tail : Fin count → alpha) :
    (Fin.cons head tail : Fin (count + 1) → alpha) ≍
      (head :: List.ofFn tail).get := by
  apply (Fin.heq_fun_iff (by simp)).2
  intro index
  refine Fin.cases ?_ (fun previous => ?_) index
  · simp
  · simp

theorem counterRoundEstimate_eq_extensionEstimator_internal
    {overhead arity rounds : ℕ} {beta : PositiveRationalScale}
    (family : ApproximateCounterFamily overhead beta arity)
    (target : BitString arity → Bool)
    (inputs : Fin rounds → BitString arity)
    (hrounds : rounds + 1 ≤ requiredRoundCount beta arity) :
    counterRoundEstimate
        (family.counter (selectionPrefixCounterIndex hrounds))
        (truthTable target) (packTargetSamples target inputs) =
      family.extensionEstimator target (List.ofFn inputs) := by
  funext input
  erw [counterRoundEstimate_truthTable_packTargetSamples_internal]
  unfold ApproximateCounterFamily.extensionEstimator
  split_ifs with hlength
  · let ExtensionData :=
      Σ index : Fin (requiredRoundCount beta arity),
        Fin (index.val + 1) → BitString arity
    let left : ExtensionData :=
      ⟨selectionPrefixCounterIndex hrounds, Fin.cons input inputs⟩
    let right : ExtensionData :=
      ⟨⟨(List.ofFn inputs).length, hlength⟩,
        (input :: List.ofFn inputs).get⟩
    let evaluate : ExtensionData → ℕ := fun data =>
      (family.counter data.1).estimate
        (packTargetSamples target data.2)
    change evaluate left = evaluate right
    apply congrArg evaluate
    have hindex : left.1 = right.1 := by
      apply Fin.ext
      simp [left, right, selectionPrefixCounterIndex]
    exact Sigma.ext hindex (finCons_heq_get_cons_ofFn input inputs)
  · exfalso
    apply hlength
    simp
    omega

private theorem packTargetSamples_elim0
    {arity : ℕ} (target : BitString arity → Bool) :
    packTargetSamples target (fun index : Fin 0 => index.elim0) =
      emptyLabeledPrefix arity := by
  funext coordinate
  exact Fin.elim0 ⟨coordinate.val, by simpa using coordinate.isLt⟩

theorem exists_eval_selectionPrefixCircuit_isEstimateSelectionTrace_internal
    {overhead arity rounds : ℕ} {beta : PositiveRationalScale}
    (family : ApproximateCounterFamily overhead beta arity)
    (target : BitString arity → Bool)
    (hrounds : rounds ≤ requiredRoundCount beta arity) :
    ∃ inputs : Fin rounds → BitString arity,
      (selectionPrefixCircuit family rounds hrounds).2.eval
          (truthTable target) = selectionTraceState target inputs ∧
        AntiChecker.IsEstimateSelectionTrace
          (family.extensionEstimator target) (List.ofFn inputs) := by
  induction rounds with
  | zero =>
      refine ⟨fun index : Fin 0 => index.elim0, ?_, ?_⟩
      · rw [eval_selectionPrefixCircuit_zero_internal]
        unfold selectionTraceState
        rw [packTargetSamples_elim0]
      · simp [AntiChecker.IsEstimateSelectionTrace]
  | succ rounds ih =>
      obtain ⟨inputs, heval, htrace⟩ :=
        ih (selectionPrefixPriorBound hrounds)
      let counter : ApproximateCounterCircuit overhead beta arity rounds :=
        family.counter (selectionPrefixCounterIndex hrounds)
      obtain ⟨candidate, hstep, hminimum⟩ :=
        exists_eval_selectionRoundStateCircuit_eq_successor
          counter (truthTable target) (packTargetSamples target inputs)
      let chosen := MCSP.Instance.inputOfIndex candidate
      refine ⟨Fin.cons chosen inputs, ?_, ?_⟩
      · calc
          (selectionPrefixCircuit family (rounds + 1) hrounds).2.eval
              (truthTable target) =
            (selectionRoundStateCircuit counter).2.eval
                ((selectionPrefixCircuit family rounds
                  (selectionPrefixPriorBound hrounds)).2.eval
                    (truthTable target)) := by
              simpa [counter] using! eval_selectionPrefixCircuit_succ_internal
                  family hrounds (truthTable target)
          _ = (selectionRoundStateCircuit counter).2.eval
                  (selectionTraceState target inputs) :=
              congrArg
                (selectionRoundStateCircuit counter).2.eval heval
          _ = (selectionRoundStateCircuit counter).2.eval
                  (selectionRoundInput (truthTable target)
                    (packTargetSamples target inputs)) := rfl
          _ = selectionRoundSuccessorInput candidate (truthTable target)
                (packTargetSamples target inputs) := hstep
          _ = selectionTraceState target (Fin.cons chosen inputs) := by
              unfold chosen
              exact
                selectionRoundSuccessorInput_truthTable_packTargetSamples_internal
                  target inputs candidate
      · have hestimator :
            counterRoundEstimate counter (truthTable target)
                (packTargetSamples target inputs) =
              family.extensionEstimator target (List.ofFn inputs) := by
          simpa [counter] using! counterRoundEstimate_eq_extensionEstimator_internal
              family target inputs hrounds
        have hminimum' :
            AntiChecker.IsEstimateMinimizer
              (family.extensionEstimator target (List.ofFn inputs)) chosen := by
          rw [← hestimator]
          exact hminimum
        rw [List.ofFn_cons]
        exact ⟨htrace, hminimum'⟩

theorem exists_eval_fullSelectionStateCircuit_isEstimateSelectionTrace_internal
    {overhead arity : ℕ} {beta : PositiveRationalScale}
    (family : ApproximateCounterFamily overhead beta arity)
    (target : BitString arity → Bool) :
    ∃ inputs : Fin (requiredRoundCount beta arity) → BitString arity,
      (fullSelectionStateCircuit family).2.eval (truthTable target) =
          selectionTraceState target inputs ∧
        AntiChecker.IsEstimateSelectionTrace
          (family.extensionEstimator target) (List.ofFn inputs) := by
  simpa [fullSelectionStateCircuit] using
    exists_eval_selectionPrefixCircuit_isEstimateSelectionTrace_internal
      family target (le_refl (requiredRoundCount beta arity))

theorem unpackSample_selectionTraceState_projection_internal
    {arity rounds : ℕ} (target : BitString arity → Bool)
    (inputs : Fin rounds → BitString arity) (sample : Fin rounds) :
    unpackSample
        (selectionTraceState target inputs ∘
          selectionSampleOutputMap arity rounds) sample =
      inputs sample := by
  funext coordinate
  show Fin.append (truthTable target) (packTargetSamples target inputs)
      (selectionSampleOutputMap arity rounds
        (finProdFinEquiv (sample, coordinate))) = _
  simp [selectionSampleOutputMap, Equiv.symm_apply_apply, Fin.append_right]

theorem eval_fullSelectionSamplesCircuit_internal
    {overhead arity : ℕ} {beta : PositiveRationalScale} [NeZero arity]
    (family : ApproximateCounterFamily overhead beta arity)
    (table : BitString (2 ^ arity)) :
    (fullSelectionSamplesCircuit family).2.eval table =
      (fullSelectionStateCircuit family).2.eval table ∘
        selectionSampleOutputMap arity (requiredRoundCount beta arity) := by
  unfold fullSelectionSamplesCircuit
  rw [Circuit.eval_compose, Circuit.eval_projectInputs]

theorem size_fullSelectionSamplesCircuit_internal
    {overhead arity : ℕ} {beta : PositiveRationalScale} [NeZero arity]
    (family : ApproximateCounterFamily overhead beta arity) :
    (fullSelectionSamplesCircuit family).2.size =
      (fullSelectionStateCircuit family).2.size +
        requiredRoundCount beta arity * arity := by
  unfold fullSelectionSamplesCircuit
  rw [Circuit.size_compose, Circuit.size_projectInputs]

theorem exists_eval_fullSelectionSamplesCircuit_isEstimateSelectionTrace_internal
    {overhead arity : ℕ} {beta : PositiveRationalScale} [NeZero arity]
    (family : ApproximateCounterFamily overhead beta arity)
    (target : BitString arity → Bool) :
    ∃ inputs : Fin (requiredRoundCount beta arity) → BitString arity,
      unpackSamples
          ((fullSelectionSamplesCircuit family).2.eval (truthTable target)) =
          List.ofFn inputs ∧
        AntiChecker.IsEstimateSelectionTrace
          (family.extensionEstimator target) (List.ofFn inputs) := by
  obtain ⟨inputs, hstate, htrace⟩ :=
    exists_eval_fullSelectionStateCircuit_isEstimateSelectionTrace_internal
      family target
  refine ⟨inputs, ?_, htrace⟩
  rw [eval_fullSelectionSamplesCircuit_internal, hstate]
  unfold unpackSamples
  apply congrArg List.ofFn
  funext sample
  exact unpackSample_selectionTraceState_projection_internal
    target inputs sample

end AntiCheckerLemma

end Magnification

end GapMCSP

end Complexity
