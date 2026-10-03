/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Defs
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Splitting.Iterated.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Condenser.Defs
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Splitting.Iterated.Family.Internal

/-!
# Multiblock splitting with a retained seed

Split every consecutive pair separately in each conditional seed fiber.
The repaired fibers form block sources, and their joint distance from the
actual split family is at most `t * 2^(-e)`. The original seed is kept
once, and no new randomness is introduced. Empty seed types use the
zero-mass convention of `seedFamilyWeight`.

This is the retained-seed version of the checked finite splitting theorem
corresponding to Chattopadhyay--Goodman--Liao, Corollary 5.4:
<https://eccc.weizmann.ac.il/report/2021/075/download/>.
-/

public section

namespace Algebraic.Cutwidth.Extractor

/-- Split a family of conditional block sources while keeping its seed,
with joint error bounded by the average splitting cost and no fresh seed. -/
theorem exists_split_pow_two_seedFamily {α Seed : Type*} [Fintype α] [Fintype Seed]
    {t m s k e : Nat} (p : Seed → (Fin t → α × α) → ℝ)
    (source : ∀ y, IsBlockSource (p y) (2 ^ k)) (card : Fintype.card α = 2 ^ m)
    (width : s ≤ m) (entropy : m + s + e ≤ k) :
    ∃ q : Seed → (Fin (2 * t) → α) → ℝ,
      (∀ y, IsBlockSource (q y) (2 ^ s)) ∧
        weightDist
          (mapWeight (fun yx : Seed × (Fin t → α × α) =>
            (yx.1, splitBlockEquiv α t yx.2)) (seedFamilyWeight p))
          (seedFamilyWeight q) ≤ (t : ℝ) * ((2 : ℝ) ^ e)⁻¹ :=
  Internal.exists_split_pow_two_seedFamily p source card width entropy

end Algebraic.Cutwidth.Extractor
