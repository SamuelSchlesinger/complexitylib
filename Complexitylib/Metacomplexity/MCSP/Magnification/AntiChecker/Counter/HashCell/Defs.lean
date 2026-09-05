/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Classes.Randomized.ApproximateCounting.Relative.Defs
public import Complexitylib.Metacomplexity.MCSP.Magnification.AntiChecker.Counter.Domain.Defs

/-!
# Hashed anti-checker survivor cells -- definitions

The existential predicate below is the exact query made by Stockmeyer's
occupancy test. A witness is a row-major tuple of encoded survivor codes in the
prescribed Cartesian power that the selected affine hash sends to zero.
-/


@[expose] public section

namespace Complexity

namespace GapMCSP

namespace Magnification

namespace AntiCheckerLemma

/-- Width of one witness tuple used by relative counting on the encoded
anti-checker survivor domain. -/
def survivorPowerWidth (arity threshold precision : ℕ) : ℕ :=
  ApproximateCounting.Relative.poweredWidth
    (candidateCodeWidth arity threshold) precision

/-- One tuple of encoded survivors belongs to the selected affine zero cell. -/
def HashCellWitness {count : ℕ}
    (arity threshold precision rangeWidth : ℕ)
    (input : BitString (count * (arity + 1)))
    (seed : BitString (PairwiseIndependentHash.affineSeedWidth
      (survivorPowerWidth arity threshold precision) rangeWidth))
    (witness : BitString (survivorPowerWidth arity threshold precision)) : Prop :=
  witness ∈ ApproximateCounting.cartesianPower
      (encodedSurvivorSet arity threshold input)
      (ApproximateCounting.relativeCopies precision) ∧
    (PairwiseIndependentHash.affine
      (survivorPowerWidth arity threshold precision) rangeWidth).eval
        seed witness = fun _ => false

instance {count : ℕ} (arity threshold precision rangeWidth : ℕ)
    (input : BitString (count * (arity + 1)))
    (seed : BitString (PairwiseIndependentHash.affineSeedWidth
      (survivorPowerWidth arity threshold precision) rangeWidth))
    (witness : BitString (survivorPowerWidth arity threshold precision)) :
    Decidable (HashCellWitness arity threshold precision rangeWidth
      input seed witness) := by
  unfold HashCellWitness
  exact @instDecidableAnd _ _ (Finset.decidableMem _ _) inferInstance

/-- The selected affine zero cell contains at least one powered survivor
witness. -/
def HashCellNonempty {count : ℕ}
    (arity threshold precision rangeWidth : ℕ)
    (input : BitString (count * (arity + 1)))
    (seed : BitString (PairwiseIndependentHash.affineSeedWidth
      (survivorPowerWidth arity threshold precision) rangeWidth)) : Prop :=
  ∃ witness, HashCellWitness arity threshold precision rangeWidth
    input seed witness

instance {count : ℕ} (arity threshold precision rangeWidth : ℕ)
    (input : BitString (count * (arity + 1)))
    (seed : BitString (PairwiseIndependentHash.affineSeedWidth
      (survivorPowerWidth arity threshold precision) rangeWidth)) :
    Decidable (HashCellNonempty arity threshold precision rangeWidth
      input seed) := by
  unfold HashCellNonempty
  infer_instance

end AntiCheckerLemma

end Magnification

end GapMCSP

end Complexity
