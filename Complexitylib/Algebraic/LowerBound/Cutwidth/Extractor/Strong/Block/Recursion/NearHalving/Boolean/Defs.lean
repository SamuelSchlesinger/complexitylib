/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.NearHalving.Codec.Defs
public import Mathlib.Logic.Equiv.Fin.Basic

/-!
# The near-halving extractor on Boolean seeds and output coordinates

Decode an exact-length Boolean seed into the retained field seeds. Read the
recursive extractor's output in block order through the standard product
index equivalence, and identify the two field elements with Boolean values.
This is a semantic representation; its string evaluator is a separate layer.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Extractor

/-- Decode the seed word and flatten the extractor's Boolean output in block order. -/
noncomputable def nearHalvingBlockBooleanExtractor (n h Q E : Nat) (x : Fin n → Bool)
    (seed : Fin (nearHalvingBlockSeedBits n h Q E) → Bool)
    (j : Fin (recursiveBlockCount 1 h * nearHalvingBlockLeafLength h Q)) : Bool :=
  let ij : Fin (recursiveBlockCount 1 h) × Fin (nearHalvingBlockLeafLength h Q) :=
    finProdFinEquiv.symm j
  decide (nearHalvingBlockExtractor n h Q E x
    (decodeNearHalvingBlockSeeds n h Q E (List.ofFn seed)) ij.1 ij.2 = 1)

end Algebraic.Cutwidth.Extractor
