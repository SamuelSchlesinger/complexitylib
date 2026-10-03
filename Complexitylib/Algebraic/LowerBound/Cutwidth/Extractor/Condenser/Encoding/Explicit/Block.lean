/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Encoding.Explicit.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Condenser.Defs
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Encoding.Explicit.Weighted
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Condenser

/-!
# The scheduled condenser on blocks with one shared seed

Apply the actual decoded scheduled map to every input block, using the
same seed for all blocks. The joint output is within `t * 2^(-e)` of a
normalized threshold-`2^k` block source conditional on each seed. The
source may have arbitrary dependence consistent with its block-source caps.

This is a finite statistical specialization of shared-seed condensation.
It does not construct an encoded runtime loop over a varying block count.
-/

public section

namespace Algebraic.Cutwidth.Extractor

/-- The scheduled map condenses any block source represented by fixed-length
words, with the same seed in every block and additive total variation error. -/
theorem decodedExplicitCondenser_block (n k e u : Nat) {α : Type*} [Fintype α]
    [Fintype (AdjoinRoot
      (binaryModulus (sparseFieldExponent u (explicitCondenserBudget n k e))))]
    (rate : 0 < u) (input : α ↪ List Bool) (sourceLength : ∀ x, (input x).length = n)
    {t : Nat} {p : (Fin t → α) → ℝ} (source : IsBlockSource p (2 ^ k)) :
    let F := AdjoinRoot (binaryModulus (sparseFieldExponent u (explicitCondenserBudget n k e)))
    let m := condenserCoordinates k (sparsePowerBits u (explicitCondenserBudget n k e))
    ∃ q : F → (Fin t → Fin m → F) → ℝ,
      (∀ y, IsBlockSource (q y) (2 ^ k)) ∧
        weightDist (weightedSeededOutput p
          (fun x y i => decodedExplicitCondenser n k e u (input (x i)) y))
          (seedFamilyWeight q) ≤ (t : ℝ) * ((2 : ℝ) ^ e)⁻¹ :=
  (decodedExplicitCondenser_weighted n k e u rate input sourceLength).block source

/-- In particular, arbitrary dependent blocks of `n` Boolean coordinates
use the scheduled condenser with one retained shared seed. -/
theorem decodedExplicitCondenser_block_ofFn (n k e u : Nat)
    [Fintype (AdjoinRoot
      (binaryModulus (sparseFieldExponent u (explicitCondenserBudget n k e))))]
    (rate : 0 < u) {t : Nat} {p : (Fin t → (Fin n → Bool)) → ℝ}
    (source : IsBlockSource p (2 ^ k)) :
    let F := AdjoinRoot (binaryModulus (sparseFieldExponent u (explicitCondenserBudget n k e)))
    let m := condenserCoordinates k (sparsePowerBits u (explicitCondenserBudget n k e))
    ∃ q : F → (Fin t → Fin m → F) → ℝ,
      (∀ y, IsBlockSource (q y) (2 ^ k)) ∧
        weightDist (weightedSeededOutput p
          (fun x y i => decodedExplicitCondenser n k e u (List.ofFn (x i)) y))
          (seedFamilyWeight q) ≤ (t : ℝ) * ((2 : ℝ) ^ e)⁻¹ :=
  (decodedExplicitCondenser_weighted_ofFn n k e u rate).block source

end Algebraic.Cutwidth.Extractor
