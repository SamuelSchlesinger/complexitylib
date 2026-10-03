/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Scheduled.Program.Defs

/-!
# The actual scheduled extractor on Boolean source and seed coordinates

Supply both input and seed as fixed-length Boolean vectors, run the actual
bit program, and read the output in block order. The seed vector has exactly
the previously specified total seed width. This definition invokes no
semantic field enumeration or abstract extractor map.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Extractor

/-- Read the actual scheduled program's output blocks at a Boolean source and seed vector. -/
def scheduledBlockBooleanExtractor (n h Q E ell : Nat) (x : Fin n → Bool)
    (seed : Fin (scheduledBlockSeedBits n h Q E ell) → Bool)
    (i : Fin (recursiveBlockCount 1 h)) (j : Fin ell) : Bool :=
  let output := scheduledBlockExtractorBits n h Q E ell (List.ofFn x) (List.ofFn seed)
  (Complexity.BitPolynomial.coefficientBlock output ell i.val)[j.val]?.getD false

end Algebraic.Cutwidth.Extractor
