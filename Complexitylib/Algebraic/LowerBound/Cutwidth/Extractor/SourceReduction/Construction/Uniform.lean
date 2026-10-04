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
public import Complexitylib.Tactic.PolyTime.Init
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.SourceReduction.Construction.Uniform.Internal
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.SourceReduction.Construction.Uniform.Internal.Basic

/-!
# One uniform polynomial-time sumset-extractor family

All parameters are generated from the original input length. The outer
count has an unconditional polynomial bound, and a cap makes the candidate
count uniformly bounded at every size. The cap is eventually inactive.
The computed family therefore has the actual extractor's constant error
and sublinear source entropy for all sufficiently large lengths.

Balanced padding gives one fixed, exactly balanced family at every positive
length and preserves its total polynomial-time evaluator. The subsequent
circuit lower bound is measured at this full padded input length.
-/

public section

namespace Algebraic.Cutwidth.Extractor

open Filter

/-- The total unpadded evaluator returns exactly one bit at every input length. -/
theorem sourceReductionFamilyEval_length (source : List Bool) :
    (sourceReductionFamilyEval source).length = 1 :=
  Internal.sourceReductionFamilyEval_length source

/-- The evaluator computes the same Boolean family at every input length. -/
theorem sourceReductionFamilyEval_ofFn (n : Nat) (x : Fin n → Bool) :
    sourceReductionFamilyEval (List.ofFn x) = [sourceReductionFamily n x] :=
  Internal.sourceReductionFamilyEval_ofFn n x

/-- All parameter generation, enumeration, actual calls, XOR, and majority are polynomial-time. -/
@[polytime] theorem sourceReductionFamilyEval_mem_FP : sourceReductionFamilyEval ∈ Complexity.FP :=
  Internal.sourceReductionFamilyEval_mem_FP

/-- Eventually the computed family equals the actual finite sumset construction exactly.
The proof needs the candidate cap `n + 1` to be inactive, and the cap binds at every positive
length with `log₂ (n + 1) < 2 ^ 27 * 70 ^ 3 ≈ 4.6 * 10 ^ 13`. The threshold here, which every
circuit bound for the hard family inherits, therefore exceeds `2 ^ (4.6 * 10 ^ 13)`. -/
theorem sourceReductionFamily_eventually_eq :
    ∀ᶠ n : Nat in atTop,
      sourceReductionFamily n = sourceReductionExtractor n (sourceReductionFamilyScale n) :=
  Internal.sourceReductionFamily_eventually_eq

/-- The one computed family eventually extracts with constant error below one half. -/
theorem sourceReductionFamily_eventually_flat :
    ∀ᶠ n : Nat in atTop, FlatSumsetExtractor (sourceReductionFamily n)
      (2 ^ sourceReductionEntropy n (sourceReductionFamilyScale n)) (35 / 72) :=
  Internal.sourceReductionFamily_eventually_flat

/-- The actual source entropy of the uniformly computed family is sublinear. -/
theorem sourceReductionFamilyEntropy_isLittleO :
    (fun n : Nat => (sourceReductionEntropy n (sourceReductionFamilyScale n) : ℝ))
      =o[atTop] (fun n => (n : ℝ)) :=
  Internal.sourceReductionFamilyEntropy_isLittleO

/-- At each positive length, the final family is precisely balanced padding. -/
theorem sourceReductionHardFamily_succ (n : Nat) :
    sourceReductionHardFamily (n + 1) = balancePad (sourceReductionFamily n) :=
  Internal.sourceReductionHardFamily_succ n

/-- Exactly half of the full padded input cube is accepted, including while the cap is active. -/
theorem sourceReductionHardFamily_card_accepting (n : Nat) :
    (accepting (sourceReductionHardFamily (n + 1))).card = 2 ^ n :=
  Internal.sourceReductionHardFamily_card_accepting n

/-- A single total evaluator computes the hard family at every input length, including zero. -/
theorem sourceReductionHardEval_ofFn (n : Nat) (x : Fin n → Bool) :
    sourceReductionHardEval (List.ofFn x) = [sourceReductionHardFamily n x] :=
  Internal.sourceReductionHardEval_ofFn n x

/-- The final balanced family has an unconditional uniform polynomial-time evaluator.
The polynomial has enormous degree: on an input of length `n + 1` the evaluator enumerates
`(2 ^ clog₂ (n + 1)) ^ (2 ^ 27) ≥ (n + 1) ^ (2 ^ 27)` outer coordinates, so its degree is at
least `2 ^ 27 ≈ 1.3 * 10 ^ 8`. -/
@[polytime] theorem sourceReductionHardEval_mem_FP : sourceReductionHardEval ∈ Complexity.FP :=
  Internal.sourceReductionHardEval_mem_FP

/-- Membership in the hard language agrees exactly with every Boolean slice. -/
theorem mem_sourceReductionHardLanguage_ofFn (n : Nat) (x : Fin n → Bool) :
    List.ofFn x ∈ sourceReductionHardLanguage ↔ sourceReductionHardFamily n x = true :=
  Internal.mem_sourceReductionHardLanguage_ofFn n x

/-- The concrete hard language has a deterministic polynomial-time decider. The decider runs
`sourceReductionHardEval`, so its polynomial also has degree at least `2 ^ 27`. -/
theorem sourceReductionHardLanguage_mem_P : sourceReductionHardLanguage ∈ Complexity.P :=
  Internal.sourceReductionHardLanguage_mem_P

end Algebraic.Cutwidth.Extractor
