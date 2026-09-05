/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.MCSP.Magnification.AntiChecker.Generator.Assembly.Defs
import Complexitylib.Metacomplexity.MCSP.Magnification.AntiChecker.Generator.Internal
import Complexitylib.Metacomplexity.MCSP.Magnification.AntiChecker.Generator.Padding.Internal
import Complexitylib.Metacomplexity.MCSP.Magnification.AntiChecker.Generator.Size.Internal
import Complexitylib.Metacomplexity.MCSP.Magnification.AntiChecker.Rounds.Internal

/-!
# Anti-checker generator assembly -- proof internals
-/


public section

namespace Complexity

namespace GapMCSP

namespace Magnification

namespace AntiCheckerLemma

theorem eventually_exists_generatorOfCounterFamily_isCorrect_internal
    (counterOverhead : ℕ) (beta : PositiveRationalScale) :
    ∀ᶠ arity : ℕ in Filter.atTop,
      ∀ (harity : arity ≠ 0),
        letI : NeZero arity := ⟨harity⟩
        ∀ (family : ApproximateCounterFamily counterOverhead beta arity),
          family.IsCorrect →
            ∃ generator :
                Generator (generatorOverheadFromCounter counterOverhead)
                  beta arity,
              generator.IsCorrect := by
  filter_upwards
      [eventually_requiredRoundCount_le_sampleCount_internal beta,
        eventually_size_paddedSelectionCircuit_le_generatorSizeBound_internal
          counterOverhead beta,
        eventually_eval_paddedSelectionCircuit_isFor_of_correctCounterFamily_internal
          beta]
      with arity hbudget hsize hsemantic
  intro harity
  let : NeZero arity := ⟨harity⟩
  intro family hcorrect
  let generator := generatorOfCounterFamily family hbudget
    (hsize harity family hbudget)
  refine ⟨generator, ?_⟩
  intro target hhard
  change
    AntiChecker.IsFor target (smallThreshold beta arity)
      (unpackSamples
        ((paddedSelectionCircuit family hbudget).2.eval
          (truthTable target)))
  exact hsemantic harity counterOverhead family hbudget hcorrect target hhard

theorem eventually_existsCorrectGeneratorAt_of_existsCorrectCounterFamilyAt_internal
    (counterOverhead : ℕ) (beta : PositiveRationalScale) :
    ∀ᶠ arity : ℕ in Filter.atTop,
      ExistsCorrectCounterFamilyAt counterOverhead beta arity →
        ExistsCorrectGeneratorAt
          (generatorOverheadFromCounter counterOverhead) beta arity := by
  filter_upwards
      [eventually_exists_generatorOfCounterFamily_isCorrect_internal
        counterOverhead beta,
        Filter.eventually_ge_atTop 1]
      with arity hgenerator harity
  intro hfamily
  have harity' : arity ≠ 0 := by omega
  let : NeZero arity := ⟨harity'⟩
  obtain ⟨family, hcorrect⟩ := hfamily
  obtain ⟨generator, hgeneratorCorrect⟩ :=
    hgenerator harity' family hcorrect
  exact
    (existsCorrectGeneratorAt_iff_of_ne_internal
      (generatorOverheadFromCounter counterOverhead) beta harity').2
        ⟨generator, hgeneratorCorrect⟩

theorem hasGenerators_of_hasApproximateCounterFamilies_internal :
    HasApproximateCounterFamilies → HasGenerators := by
  rintro ⟨counterOverhead, hfamilies⟩
  refine ⟨generatorOverheadFromCounter counterOverhead,
    Filter.Eventually.of_forall (fun beta => ?_)⟩
  filter_upwards
      [hfamilies beta,
        eventually_existsCorrectGeneratorAt_of_existsCorrectCounterFamilyAt_internal
          counterOverhead beta]
      with arity hfamily hgenerator
  exact hgenerator hfamily

end AntiCheckerLemma

end Magnification

end GapMCSP

end Complexity
