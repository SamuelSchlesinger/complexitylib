/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.MCSP.Magnification.AntiChecker.Generator.Defs
import Complexitylib.Metacomplexity.MCSP
import Complexitylib.Metacomplexity.MCSP.AntiChecker
import Complexitylib.Metacomplexity.MCSP.Magnification.AntiChecker.Parameters
import Complexitylib.Metacomplexity.ScaledExponent

/-!
# Typed Anti-Checker Lemma generators -- proof internals
-/


public section

namespace Complexity

namespace GapMCSP

namespace Magnification

namespace AntiCheckerLemma

theorem unpackSample_apply_internal {count arity : ℕ}
    (output : BitString (count * arity)) (sample : Fin count)
    (coordinate : Fin arity) :
    unpackSample output sample coordinate =
      output (finProdFinEquiv (sample, coordinate)) := rfl

theorem length_unpackSamples_internal {count arity : ℕ}
    (output : BitString (count * arity)) :
    (unpackSamples output).length = count := by
  simp [unpackSamples]

theorem getElem_unpackSamples_internal {count arity : ℕ}
    (output : BitString (count * arity)) (sample : Fin count) :
    (unpackSamples output)[sample.val]'(by
      rw [length_unpackSamples_internal output]
      exact sample.isLt) = unpackSample output sample := by
  simp [unpackSamples]

theorem truthTable_inputIndex_internal {arity : ℕ}
    (target : BitString arity → Bool) (input : BitString arity) :
    truthTable target (MCSP.Instance.inputIndex input) = target input := by
  have hfunction :=
    congrFun (MCSP.Instance.function_ofFunction arity 0 target) input
  simpa [truthTable, MCSP.Instance.function] using hfunction

theorem isHardAt_iff_minimumSize_gt_internal {arity : ℕ}
    (beta : PositiveRationalScale) (target : BitString arity → Bool) :
    IsHardAt beta target ↔
      hardThreshold beta arity <
        (MCSP.Instance.ofFunction arity
          (hardThreshold beta arity) target).minimumSize := by
  rw [IsHardAt, MCSP.Instance.hasCircuitAtMost_iff_minimumSize_le]
  simp

theorem isHardAt_iff_sizeComplexity_gt_internal {arity : ℕ}
    [NeZero arity] (beta : PositiveRationalScale)
    (target : BitString arity → Bool) :
    IsHardAt beta target ↔
      hardThreshold beta arity <
        Circuit.sizeComplexity Basis.andOr2 target := by
  let : NeZero
      (MCSP.Instance.ofFunction arity
        (hardThreshold beta arity) target).arity :=
    ⟨by simpa using NeZero.ne arity⟩
  rw [isHardAt_iff_minimumSize_gt_internal,
    MCSP.Instance.minimumSize_eq_sizeComplexity]
  simp

namespace Generator

theorem length_inputs_internal {overhead arity : ℕ}
    {beta : PositiveRationalScale} [NeZero arity]
    (generator : Generator overhead beta arity)
    (table : BitString (2 ^ arity)) :
    (generator.inputs table).length = sampleCount beta arity := by
  exact length_unpackSamples_internal (generator.circuit.eval table)

theorem length_inputsFor_internal {overhead arity : ℕ}
    {beta : PositiveRationalScale} [NeZero arity]
    (generator : Generator overhead beta arity)
    (target : BitString arity → Bool) :
    (generator.inputsFor target).length = sampleCount beta arity :=
  length_inputs_internal generator (truthTable target)

theorem outputBitCount_le_sizeBound_internal {overhead arity : ℕ}
    {beta : PositiveRationalScale} [NeZero arity]
    (generator : Generator overhead beta arity) :
    outputBitCount beta arity ≤
      generatorSizeBound overhead beta arity := by
  apply le_trans _ generator.size_le
  simp [Circuit.size]

theorem isCorrect_iff_encode_not_mem_internal {overhead arity : ℕ}
    {beta : PositiveRationalScale} [NeZero arity]
    (generator : Generator overhead beta arity) :
    generator.IsCorrect ↔
      ∀ target, IsHardAt beta target →
        (SuccinctMCSP.Instance.ofInputs (smallThreshold beta arity)
          target (generator.inputsFor target)).encode ∉
            Complexity.SuccinctMCSP := by
  constructor
  · intro hcorrect target hhard
    exact (Complexity.AntiChecker.encode_not_mem_iff_isFor
      target (generator.inputsFor target)).mpr
        (hcorrect target hhard)
  · intro hreject target hhard
    exact (Complexity.AntiChecker.encode_not_mem_iff_isFor
      target (generator.inputsFor target)).mp
        (hreject target hhard)

end Generator

theorem existsCorrectGeneratorAt_iff_of_ne_internal
    (overhead : ℕ) (beta : PositiveRationalScale) {arity : ℕ}
    (harity : arity ≠ 0) :
    ExistsCorrectGeneratorAt overhead beta arity ↔
      letI : NeZero arity := ⟨harity⟩
      ∃ generator : Generator overhead beta arity, generator.IsCorrect := by
  simp [ExistsCorrectGeneratorAt, harity]

theorem hasGenerators_iff_cutoff_internal :
    HasGenerators ↔
      ∃ (overhead : ℕ) (cutoff : PositiveRationalScale),
        ∀ beta ≤ cutoff,
          ∀ᶠ arity in Filter.atTop,
            ExistsCorrectGeneratorAt overhead beta arity := by
  unfold HasGenerators
  constructor
  · rintro ⟨overhead, hgenerators⟩
    obtain ⟨cutoff, hgenerators⟩ :=
      (PositiveRationalScale.eventually_atZeroFromPositive_iff).mp
        hgenerators
    exact ⟨overhead, cutoff, hgenerators⟩
  · rintro ⟨overhead, cutoff, hgenerators⟩
    exact ⟨overhead,
      (PositiveRationalScale.eventually_atZeroFromPositive_iff).mpr
        ⟨cutoff, hgenerators⟩⟩

end AntiCheckerLemma

end Magnification

end GapMCSP

end Complexity
