/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.SourceReduction.Construction.Uniform.Defs
public import Complexitylib.Classes.P.Defs
public import Mathlib.Analysis.Asymptotics.Defs
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.SourceReduction.Construction.Uniform.Internal.Parameters
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.SourceReduction.Construction.Asymptotics
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.SourceReduction.Construction.Program
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Padding
import Complexitylib.Classes.P.DecisionFn
import Complexitylib.Tactic.PolyTime

/-!
# Uniform computation and eventual extraction of the same fixed family

The candidate cap makes enumeration polynomial-time at every length.
Its eventual inactivity identifies the computed family with the actual
finite extractor. Thus the statistical and computational theorems concern
one fixed family, with no supplied algorithm or asymptotic hypothesis.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

open Filter Complexity

theorem sourceReductionFamilyEval_mem_FP : sourceReductionFamilyEval ∈ FP := by
  exact sourceReductionRuntime_mem_FP
    (sourceReductionFamilyScale_unary (by polytime))
    (sourceReductionFamilyOuterCount_unary (by polytime))
    (sourceReductionBoundedCandidates_unary (by polytime)) (by polytime)

theorem sourceReductionHardEval_mem_FP : sourceReductionHardEval ∈ FP :=
  balancePadEval_mem_FP sourceReductionFamilyEval_mem_FP

theorem sourceReductionHardLanguage_mem_P : sourceReductionHardLanguage ∈ Complexity.P := by
  exact mem_P_of_decisionFn_bool
    (g := fun source => (sourceReductionHardEval source).headD false)
    sourceReductionHardEval_mem_FP (fun _ => Iff.rfl)

theorem sourceReductionFamily_eventually_eq :
    ∀ᶠ n : Nat in atTop,
      sourceReductionFamily n = sourceReductionExtractor n (sourceReductionFamilyScale n) := by
  filter_upwards [eventually_sourceReductionCandidateCount_le,
    eventually_sourceReduction_guards] with n count guards
  have cap : sourceReductionBoundedCandidates n =
      sourceReductionCandidateCount (matchedBlockSeedBits (sourceReductionFamilyScale n)) :=
    min_eq_left count
  funext x
  have program := sourceReductionRuntime_eq n (sourceReductionFamilyScale n)
    (sourceReductionOuterCount (matchedBlockSeedBits (sourceReductionFamilyScale n)))
    (sourceReductionBoundedCandidates n) rfl cap guards.2.1 x
  simpa only [sourceReductionFamily, sourceReductionFamilyEval, List.length_ofFn,
    List.headD_cons] using congrArg (fun output : List Bool => output.headD false) program

theorem sourceReductionFamily_eventually_flat :
    ∀ᶠ n : Nat in atTop, FlatSumsetExtractor (sourceReductionFamily n)
      (2 ^ sourceReductionEntropy n (sourceReductionFamilyScale n)) (35 / 72) := by
  filter_upwards [sourceReductionFamily_eventually_eq,
    eventually_sourceReductionExtractor_flat] with n identity extract
  rw [identity]
  exact extract

theorem sourceReductionFamilyEntropy_isLittleO :
    (fun n : Nat => (sourceReductionEntropy n (sourceReductionFamilyScale n) : ℝ))
      =o[atTop] (fun n => (n : ℝ)) :=
  sourceReductionEntropy_isLittleO

end Algebraic.Cutwidth.Extractor.Internal
