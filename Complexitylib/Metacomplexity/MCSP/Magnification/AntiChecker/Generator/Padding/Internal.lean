/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.MCSP.Magnification.AntiChecker.Generator.Padding.Defs
import Complexitylib.Circuits.Composition
import Complexitylib.Circuits.InputSources
import Complexitylib.Metacomplexity.MCSP.AntiChecker.Internal
import Complexitylib.Metacomplexity.MCSP.Magnification.AntiChecker.Counter.Estimator.Internal
import Complexitylib.Metacomplexity.MCSP.Magnification.AntiChecker.Generator.Iteration.Internal
import Complexitylib.Metacomplexity.MCSP.Magnification.AntiChecker.Rounds.Internal

/-!
# Anti-checker generator output padding -- proof internals
-/


public section

namespace Complexity

namespace GapMCSP

namespace Magnification

namespace AntiCheckerLemma

theorem unpackSample_padPackedSamples_internal
    {sourceCount targetCount arity : ℕ}
    (hbudget : sourceCount ≤ targetCount)
    (input : BitString (sourceCount * arity)) (sample : Fin targetCount) :
    unpackSample (padPackedSamples hbudget input) sample =
      Fin.append
        (fun _ : Fin (targetCount - sourceCount) =>
          (fun _ : Fin arity => false))
        (unpackSample input)
        (Fin.cast (Nat.sub_add_cancel hbudget).symm sample) := by
  funext coordinate
  unfold unpackSample padPackedSamples
  dsimp only
  simp only [Equiv.symm_apply_apply]
  let split := Fin.cast (Nat.sub_add_cancel hbudget).symm sample
  change
    Fin.append
        (fun _ : Fin (targetCount - sourceCount) => false)
        (fun sourceSample => input (finProdFinEquiv (sourceSample, coordinate)))
        split =
      Fin.append
          (fun _ : Fin (targetCount - sourceCount) =>
            (fun _ : Fin arity => false))
          (unpackSample input) split coordinate
  refine Fin.addCases ?_ ?_ split
  · intro paddingSample
    simp only [Fin.append_left]
  · intro sourceSample
    simp only [Fin.append_right]
    rfl

theorem unpackSamples_padPackedSamples_internal
    {sourceCount targetCount arity : ℕ}
    (hbudget : sourceCount ≤ targetCount)
    (input : BitString (sourceCount * arity)) :
    unpackSamples (padPackedSamples hbudget input) =
      AntiChecker.padInputsTo targetCount (unpackSamples input) := by
  let zero : BitString arity := fun _ => false
  let rows := Fin.append
    (fun _ : Fin (targetCount - sourceCount) => zero)
    (unpackSample input)
  have hrows :
      (fun sample : Fin targetCount =>
        unpackSample (padPackedSamples hbudget input) sample) =
      fun sample =>
        rows (Fin.cast (Nat.sub_add_cancel hbudget).symm sample) := by
    funext sample
    exact unpackSample_padPackedSamples_internal hbudget input sample
  unfold unpackSamples
  change List.ofFn
      (fun sample => unpackSample (padPackedSamples hbudget input) sample) = _
  rw [hrows]
  rw [← List.ofFn_congr (Nat.sub_add_cancel hbudget) rows]
  simp [rows, zero, AntiChecker.padInputsTo]

theorem eval_packedSamplePaddingSource_internal
    {sourceCount targetCount arity : ℕ}
    (hbudget : sourceCount ≤ targetCount)
    (input : BitString (sourceCount * arity))
    (output : Fin (targetCount * arity)) :
    (packedSamplePaddingSource hbudget output).eval input =
      padPackedSamples hbudget input output := by
  unfold packedSamplePaddingSource padPackedSamples
  let position := finProdFinEquiv.symm output
  let split := Fin.cast (Nat.sub_add_cancel hbudget).symm position.1
  change
    ((Fin.addCases
        (fun _ : Fin (targetCount - sourceCount) =>
          Circuit.InputSource.constant false)
        (fun sourceSample : Fin sourceCount =>
          Circuit.InputSource.input
            (finProdFinEquiv (sourceSample, position.2)))
        split : Circuit.InputSource (sourceCount * arity)).eval input) =
      Fin.append
        (fun _ : Fin (targetCount - sourceCount) => false)
        (fun sourceSample => unpackSample input sourceSample position.2)
        split
  refine Fin.addCases ?_ ?_ split
  · intro paddingSample
    simp [Circuit.InputSource.eval]
  · intro sourceSample
    simp [Circuit.InputSource.eval, unpackSample]

theorem eval_packedSamplePaddingCircuit_internal
    {sourceCount targetCount arity : ℕ}
    [NeZero (sourceCount * arity)] [NeZero (targetCount * arity)]
    (hbudget : sourceCount ≤ targetCount)
    (input : BitString (sourceCount * arity)) :
    (packedSamplePaddingCircuit (arity := arity) hbudget).eval input =
      padPackedSamples hbudget input := by
  unfold packedSamplePaddingCircuit
  rw [Circuit.eval_inputSources]
  funext output
  exact eval_packedSamplePaddingSource_internal hbudget input output

theorem size_packedSamplePaddingCircuit_internal
    {sourceCount targetCount arity : ℕ}
    [NeZero (sourceCount * arity)] [NeZero (targetCount * arity)]
    (hbudget : sourceCount ≤ targetCount) :
    (packedSamplePaddingCircuit (arity := arity) hbudget).size =
      targetCount * arity := by
  simp [Circuit.size]

theorem eval_paddedSelectionCircuit_internal
    {overhead arity : ℕ} {beta : PositiveRationalScale} [NeZero arity]
    (family : ApproximateCounterFamily overhead beta arity)
    (hbudget : requiredRoundCount beta arity ≤ sampleCount beta arity)
    (table : BitString (2 ^ arity)) :
    (paddedSelectionCircuit family hbudget).2.eval table =
      padPackedSamples hbudget
        ((fullSelectionSamplesCircuit family).2.eval table) := by
  unfold paddedSelectionCircuit
  change
    ((packedSamplePaddingCircuit (arity := arity) hbudget).compose
      (fullSelectionSamplesCircuit family).2).eval table = _
  rw [Circuit.eval_compose, eval_packedSamplePaddingCircuit_internal]

theorem size_paddedSelectionCircuit_internal
    {overhead arity : ℕ} {beta : PositiveRationalScale} [NeZero arity]
    (family : ApproximateCounterFamily overhead beta arity)
    (hbudget : requiredRoundCount beta arity ≤ sampleCount beta arity) :
    (paddedSelectionCircuit family hbudget).2.size =
      (fullSelectionSamplesCircuit family).2.size +
        outputBitCount beta arity := by
  unfold paddedSelectionCircuit outputBitCount
  change
    ((packedSamplePaddingCircuit (arity := arity) hbudget).compose
      (fullSelectionSamplesCircuit family).2).size = _
  rw [Circuit.size_compose, size_packedSamplePaddingCircuit_internal]

theorem exists_eval_paddedSelectionCircuit_isEstimateSelectionTrace_internal
    {overhead arity : ℕ} {beta : PositiveRationalScale} [NeZero arity]
    (family : ApproximateCounterFamily overhead beta arity)
    (hbudget : requiredRoundCount beta arity ≤ sampleCount beta arity)
    (target : BitString arity → Bool) :
    ∃ inputs : Fin (requiredRoundCount beta arity) → BitString arity,
      unpackSamples
          ((paddedSelectionCircuit family hbudget).2.eval
            (truthTable target)) =
          AntiChecker.padInputsTo (sampleCount beta arity)
            (List.ofFn inputs) ∧
        AntiChecker.IsEstimateSelectionTrace
          (family.extensionEstimator target) (List.ofFn inputs) := by
  obtain ⟨inputs, heval, htrace⟩ :=
    exists_eval_fullSelectionSamplesCircuit_isEstimateSelectionTrace_internal
      family target
  refine ⟨inputs, ?_, htrace⟩
  rw [eval_paddedSelectionCircuit_internal,
    unpackSamples_padPackedSamples_internal, heval]

theorem eventually_eval_paddedSelectionCircuit_isFor_of_correctCounterFamily_internal
    (beta : PositiveRationalScale) :
    ∀ᶠ arity : ℕ in Filter.atTop,
      ∀ (harity : arity ≠ 0),
        letI : NeZero arity := ⟨harity⟩
        ∀ (overhead : ℕ)
          (family : ApproximateCounterFamily overhead beta arity)
          (hbudget : requiredRoundCount beta arity ≤ sampleCount beta arity),
          family.IsCorrect →
            ∀ target : BitString arity → Bool,
              IsHardAt beta target →
                AntiChecker.IsFor target (smallThreshold beta arity)
                  (unpackSamples
                    ((paddedSelectionCircuit family hbudget).2.eval
                      (truthTable target))) := by
  filter_upwards
      [eventually_padInputsTo_isFor_of_isEstimateSelectionTrace_internal beta]
      with arity hanti
  intro harity
  let : NeZero arity := ⟨harity⟩
  intro overhead family hbudget hcorrect target hhard
  obtain ⟨inputs, heval, htrace⟩ :=
    exists_eval_paddedSelectionCircuit_isEstimateSelectionTrace_internal
      family hbudget target
  rw [heval]
  exact (hanti harity target (family.extensionEstimator target)
    (List.ofFn inputs) hhard
    (ApproximateCounterFamily.isAccurateRequiredRoundEstimator_internal
      hcorrect target) (by simp) htrace).2

end AntiCheckerLemma

end Magnification

end GapMCSP

end Complexity
