/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.NearHalving.Program.Defs
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.NearHalving.Boolean.Defs
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.NearHalving.Program.Correctness.Internal

/-!
# The complete bit program computes the near-halving extractor

At the exact seed word, the runtime output is the specified recursive
extractor serialized in block order. It is also precisely the flat Boolean
output vector used by the strong-extraction theorem. Arbitrary bits after
the prescribed seed word are ignored because both final seeds are read at
their exact widths.

These identities hold for every parameter choice, including zero depth and
empty outputs, without entropy, reserve, or field-enumeration premises.
Statistical and polynomial-time bounds are established in separate layers
and therefore apply to this same map.
-/

public section

namespace Algebraic.Cutwidth.Extractor

/-- Canonical semantic seeds followed by any extra bits produce exactly the semantic tuple. -/
theorem nearHalvingBlockExtractorBits_append_eq_nearHalvingBlockExtractor (n h Q E : Nat)
    (x : Fin n → Bool) (seeds : NearHalvingBlockSeeds n h Q E) (tail : List Bool) :
    nearHalvingBlockExtractorBits n h Q E (nearHalvingBlockLeafLength h Q) h (List.ofFn x)
        (encodeNearHalvingBlockSeeds n h Q E seeds ++ tail) =
      (List.ofFn fun i => List.ofFn fun j =>
        decide (nearHalvingBlockExtractor n h Q E x seeds i j = 1)).flatten :=
  Internal.nearHalvingBlockExtractorBits_append_eq_nearHalvingBlockExtractor n h Q E x seeds tail

/-- The complete runtime word is exactly the statistical extractor's serialized output. -/
theorem nearHalvingBlockExtractorBits_eq_nearHalvingBlockExtractor (n h Q E : Nat)
    (x : Fin n → Bool) (seeds : NearHalvingBlockSeeds n h Q E) :
    nearHalvingBlockExtractorBits n h Q E (nearHalvingBlockLeafLength h Q) h (List.ofFn x)
        (encodeNearHalvingBlockSeeds n h Q E seeds) =
      (List.ofFn fun i => List.ofFn fun j =>
        decide (nearHalvingBlockExtractor n h Q E x seeds i j = 1)).flatten :=
  Internal.nearHalvingBlockExtractorBits_eq_nearHalvingBlockExtractor n h Q E x seeds

/-- An exact Boolean seed word with arbitrary trailing padding computes the same Boolean map. -/
theorem nearHalvingBlockExtractorBits_append_eq_nearHalvingBlockBooleanExtractor (n h Q E : Nat)
    (x : Fin n → Bool) (seed : Fin (nearHalvingBlockSeedBits n h Q E) → Bool)
    (tail : List Bool) :
    nearHalvingBlockExtractorBits n h Q E (nearHalvingBlockLeafLength h Q) h (List.ofFn x)
        (List.ofFn seed ++ tail) = List.ofFn (nearHalvingBlockBooleanExtractor n h Q E x seed) :=
  Internal.nearHalvingBlockExtractorBits_append_eq_nearHalvingBlockBooleanExtractor n h Q E x seed tail

/-- Listing the actual Boolean-vector extractor agrees with the complete runtime program. -/
theorem nearHalvingBlockExtractorBits_eq_nearHalvingBlockBooleanExtractor (n h Q E : Nat)
    (x : Fin n → Bool) (seed : Fin (nearHalvingBlockSeedBits n h Q E) → Bool) :
    nearHalvingBlockExtractorBits n h Q E (nearHalvingBlockLeafLength h Q) h (List.ofFn x)
        (List.ofFn seed) = List.ofFn (nearHalvingBlockBooleanExtractor n h Q E x seed) :=
  Internal.nearHalvingBlockExtractorBits_eq_nearHalvingBlockBooleanExtractor n h Q E x seed

end Algebraic.Cutwidth.Extractor
