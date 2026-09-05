/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.MCSP.Magnification.AntiChecker.Counter.HashCell.Defs
import Complexitylib.Classes.Randomized.ApproximateCounting.Power
import Complexitylib.Classes.Randomized.Hashing.Affine

/-!
# Hashed anti-checker survivor cells -- proof internals
-/


public section

namespace Complexity

namespace GapMCSP

namespace Magnification

namespace AntiCheckerLemma

theorem hashCellWitness_iff_blocks_internal
    {count arity threshold precision rangeWidth : ℕ}
    (input : BitString (count * (arity + 1)))
    (seed : BitString (PairwiseIndependentHash.affineSeedWidth
      (survivorPowerWidth arity threshold precision) rangeWidth))
    (witness : BitString (survivorPowerWidth arity threshold precision)) :
    HashCellWitness arity threshold precision rangeWidth input seed witness ↔
      (∀ copy : Fin (ApproximateCounting.relativeCopies precision),
        blocksEquiv
            (ApproximateCounting.relativeCopies precision)
            (candidateCodeWidth arity threshold) witness copy ∈
          encodedSurvivorSet arity threshold input) ∧
      (PairwiseIndependentHash.affine
          (survivorPowerWidth arity threshold precision) rangeWidth).eval
        seed witness = fun _ => false := by
  unfold HashCellWitness survivorPowerWidth
    ApproximateCounting.Relative.poweredWidth
  erw [ApproximateCounting.mem_cartesianPower_iff]

theorem hashCellNonempty_iff_cellNonempty_internal
    {count arity threshold precision rangeWidth : ℕ}
    (input : BitString (count * (arity + 1)))
    (seed : BitString (PairwiseIndependentHash.affineSeedWidth
      (survivorPowerWidth arity threshold precision) rangeWidth)) :
    HashCellNonempty arity threshold precision rangeWidth input seed ↔
      ((PairwiseIndependentHash.affine
          (survivorPowerWidth arity threshold precision) rangeWidth).cell
        (ApproximateCounting.cartesianPower
          (encodedSurvivorSet arity threshold input)
          (ApproximateCounting.relativeCopies precision))
        (fun _ => false) seed).Nonempty := by
  unfold HashCellNonempty HashCellWitness PairwiseIndependentHash.cell
  constructor
  · rintro ⟨witness, hmember, hhash⟩
    exact ⟨witness, Finset.mem_filter.mpr ⟨hmember, hhash⟩⟩
  · rintro ⟨witness, hmember⟩
    exact ⟨witness, (Finset.mem_filter.mp hmember).1,
      (Finset.mem_filter.mp hmember).2⟩

theorem hashCellNonempty_iff_cellSize_pos_internal
    {count arity threshold precision rangeWidth : ℕ}
    (input : BitString (count * (arity + 1)))
    (seed : BitString (PairwiseIndependentHash.affineSeedWidth
      (survivorPowerWidth arity threshold precision) rangeWidth)) :
    HashCellNonempty arity threshold precision rangeWidth input seed ↔
      0 < (PairwiseIndependentHash.affine
          (survivorPowerWidth arity threshold precision) rangeWidth).cellSize
        (ApproximateCounting.cartesianPower
          (encodedSurvivorSet arity threshold input)
          (ApproximateCounting.relativeCopies precision))
        (fun _ => false) seed := by
  rw [hashCellNonempty_iff_cellNonempty_internal]
  exact Finset.card_pos.symm

end AntiCheckerLemma

end Magnification

end GapMCSP

end Complexity
