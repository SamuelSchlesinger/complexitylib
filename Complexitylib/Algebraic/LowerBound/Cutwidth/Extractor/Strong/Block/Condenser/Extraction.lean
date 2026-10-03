/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Defs
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Condenser.Extraction.Internal

/-!
# Strong extraction from all blocks with one shared seed

A strong seeded extractor applied to every block of a block source has
joint seed-output error at most the number of blocks times its one-block
error. The output comparison is uniform on the entire block tuple, and
the same original seed is retained once.

The proof specializes shared-seed block condensation to full output
entropy. It is the extraction case of the finite block argument in
Chattopadhyay--Goodman--Liao, Lemma 5.5 of *Affine Extractors for Almost
Logarithmic Entropy*, <https://eccc.weizmann.ac.il/report/2021/075/>.
-/

public section

namespace Algebraic.Cutwidth.Extractor

/-- Applying a strong extractor to all blocks with one shared seed gives
uniform output tuples with joint test error at most the sum of the block errors. -/
theorem WeightedStrongSeededExtractor.block {α Seed Ω : Type*}
    [Fintype α] [Fintype Seed] [Fintype Ω] [Nonempty Seed] [Nonempty Ω]
    {E : α → Seed → Ω} {K : Nat} {ε : ℝ}
    (extract : WeightedStrongSeededExtractor E K ε) {t : Nat}
    {p : (Fin t → α) → ℝ} (source : IsBlockSource p K)
    (T : Finset (Seed × (Fin t → Ω))) :
    |weightedSeededTestProb p (fun x y i => E (x i) y) T -
      uniformSeededTestProb T| ≤ (t : ℝ) * ε :=
  Internal.weightedStrongSeededExtractor_block extract source T

end Algebraic.Cutwidth.Extractor
