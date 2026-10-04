/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.SourceReduction.Construction.Uniform.Defs
public import Complexitylib.Classes.P.Unary.Defs
import Complexitylib.Classes.P.Unary
import Complexitylib.Tactic.PolyTime
import Mathlib.Tactic.Ring

/-!
# Polynomial-time generation of the global enumeration bounds

The outer count is exactly a fixed power of `2 ^ clog 2 (n+1)`, which has
a unary polynomial-time certificate. Only the candidate count needs a cap.
Its capped power is uniformly computable even before the asymptotic
parameter conditions hold.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

open Complexity

theorem sourceReductionFamilyScale_unary {n : List Bool → Nat} (hn : UnaryFn n) :
    UnaryFn (fun z => sourceReductionFamilyScale (n z)) := by
  polytime [sourceReductionFamilyScale]

theorem sourceReductionFamilyOuterCount_unary {n : List Bool → Nat} (hn : UnaryFn n) :
    UnaryFn (fun z => sourceReductionOuterCount
      (matchedBlockSeedBits (sourceReductionFamilyScale (n z)))) := by
  have rounded := (UnaryFn.const 2).pow_clog (hn.add (UnaryFn.const 1))
  refine (rounded.pow_const (8 * 2 ^ 24)).of_eq fun z => ?_
  change (2 ^ Nat.clog 2 (n z + 1)) ^ (8 * 2 ^ 24) =
    2 ^ (8 * (2 ^ 24 * Nat.clog 2 (n z + 1)))
  rw [← pow_mul]
  congr 1
  ring

theorem sourceReductionBoundedCandidates_unary {n : List Bool → Nat} (hn : UnaryFn n) :
    UnaryFn (fun z => sourceReductionBoundedCandidates (n z)) := by
  apply (UnaryFn.const 2).powMin ?_ (hn.add (UnaryFn.const 1))
  polytime [sourceReductionCandidateBits, gammaBlockSeedBudget, gammaBlockLog, matchedBlockSeedBits,
    sourceReductionFamilyScale]

end Algebraic.Cutwidth.Extractor.Internal
