/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Classes.Randomized.Hashing.Affine.Defs
import Complexitylib.Classes.Randomized.Hashing.Affine.Internal

/-!
# Affine pairwise-independent hashing

This module constructs the standard affine family over the Boolean ring. A
hash from `domainWidth` bits to `rangeWidth` bits uses exactly
`rangeWidth * (domainWidth + 1)` random bits.
-/


public section

namespace Complexity

namespace PairwiseIndependentHash

/-- The standard affine pairwise-independent hash family over the Boolean
ring, represented by a row-major flat bit-string seed. -/
def affine (domainWidth rangeWidth : ℕ) :
    PairwiseIndependentHash domainWidth rangeWidth
      (affineSeedWidth domainWidth rangeWidth) where
  eval := affineEval
  uniform := affine_uniform_internal
  pairwise := affine_pairwise_internal

/-- Evaluation of the affine family is the concrete Boolean-ring matrix map. -/
@[simp] theorem affine_eval (domainWidth rangeWidth : ℕ) :
    (affine domainWidth rangeWidth).eval = affineEval := by simp [affine]

end PairwiseIndependentHash

end Complexity
