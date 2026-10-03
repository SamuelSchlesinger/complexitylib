/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.NearHalving.Boolean.Defs
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.NearHalving.Parameters.Explicit
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion

/-!
# The finite ordinary Gamma extractor

At target width `b`, use the selected near-halving construction on `8*b`
source bits and keep exactly its first `b` output coordinates. The complete
Boolean seed retains all level seeds and the final one-shot pair once.
Output coverage holds on every input size; the statistical guarantee uses
the separate size guard. The encoded evaluator is a separate layer.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Extractor

/-- The complete number of Boolean seed bits used by the selected construction. -/
def gammaBlockSeedBits (b : Nat) : Nat :=
  nearHalvingBlockSeedBits (8 * b) (gammaBlockDepth b) (gammaBlockReserve b)
    (gammaBlockErrorExponent b)

/-- The actual near-halving Boolean extractor, truncated to the desired output length. -/
noncomputable def gammaBlockExtractor (b : Nat) (x : Fin (8 * b) → Bool)
    (seed : Fin (gammaBlockSeedBits b) → Bool) (j : Fin b) : Bool :=
  nearHalvingBlockBooleanExtractor (8 * b) (gammaBlockDepth b) (gammaBlockReserve b)
    (gammaBlockErrorExponent b) x seed
    (Fin.castLE (by
      simpa only [recursiveBlockCount_eq, Nat.mul_one, ← gammaBlockLeafLength_eq] using
        gammaBlock_output_ge b) j)

end Algebraic.Cutwidth.Extractor
