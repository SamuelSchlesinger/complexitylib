/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.NearHalving.Defs

/-!
# Flat seed words for the near-halving recursion

The trivial initial seed occupies no bits. Fresh field seeds follow in
increasing level order, then the final condenser and hash seeds. Each field
uses its canonical coefficient word, and the final concatenation is grouped
as `(prefix ++ condenser) ++ hash`.

Decoding is total on arbitrary words. Exact inverse laws apply to words of
the prescribed length. These semantic codecs use no field enumeration.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Extractor

/-- Total width of the first `i` fresh field seeds, with an empty initial prefix. -/
def nearHalvingBlockSeedPrefixBits (n h Q E i : Nat) : Nat :=
  (Finset.range i).sum (nearHalvingBlockSeedWidth n h Q E)

/-- Encode fresh seeds in level order; the initial `Unit` seed contributes no bits. -/
noncomputable def encodeNearHalvingBlockSeedPrefix (n h Q E : Nat) :
    (i : Nat) → RecursiveSeeds Unit (NearHalvingBlockLevelSeed n h Q E) i → List Bool
  | 0, _ => []
  | i + 1, seeds => encodeNearHalvingBlockSeedPrefix n h Q E i seeds.1 ++
      BinaryFieldCodec.encode (sparseFieldExponent (nearHalvingBlockRate h)
        (explicitCondenserBudget (nearHalvingBlockWidth n h Q E i)
          (nearHalvingBlockEntropy h Q i) E)) seeds.2

/-- Decode a prefix by splitting off its last fresh field word at the prior width. -/
noncomputable def decodeNearHalvingBlockSeedPrefix (n h Q E : Nat) :
    (i : Nat) → List Bool → RecursiveSeeds Unit (NearHalvingBlockLevelSeed n h Q E) i
  | 0, _ => ()
  | i + 1, bits =>
      (decodeNearHalvingBlockSeedPrefix n h Q E i
        (bits.take (nearHalvingBlockSeedPrefixBits n h Q E i)),
       BinaryFieldCodec.decode (sparseFieldExponent (nearHalvingBlockRate h)
         (explicitCondenserBudget (nearHalvingBlockWidth n h Q E i)
           (nearHalvingBlockEntropy h Q i) E))
           (bits.drop (nearHalvingBlockSeedPrefixBits n h Q E i)))

/-- Encode the recursive seed prefix, final condenser seed, then final hash seed. -/
noncomputable def encodeNearHalvingBlockSeeds (n h Q E : Nat)
    (seeds : NearHalvingBlockSeeds n h Q E) : List Bool :=
  let width := nearHalvingBlockWidth n h Q E h
  let ell := nearHalvingBlockLeafLength h Q
  (encodeNearHalvingBlockSeedPrefix n h Q E h seeds.1 ++
    BinaryFieldCodec.encode (oneShotCondenserExponent width ell E) seeds.2.1) ++
      BinaryFieldCodec.encode (oneShotHashExponent width ell E) seeds.2.2

/-- Decode the recursive prefix and final two field words at their fixed offsets. -/
noncomputable def decodeNearHalvingBlockSeeds (n h Q E : Nat) (bits : List Bool) :
    NearHalvingBlockSeeds n h Q E :=
  let width := nearHalvingBlockWidth n h Q E h
  let ell := nearHalvingBlockLeafLength h Q
  let prefixWidth := nearHalvingBlockSeedPrefixBits n h Q E h
  let finalCondenser := 2 * 3 ^ oneShotCondenserExponent width ell E
  (decodeNearHalvingBlockSeedPrefix n h Q E h (bits.take prefixWidth),
    (BinaryFieldCodec.decode (oneShotCondenserExponent width ell E)
      ((bits.drop prefixWidth).take finalCondenser),
     BinaryFieldCodec.decode (oneShotHashExponent width ell E)
      (bits.drop (prefixWidth + finalCondenser))))

end Algebraic.Cutwidth.Extractor
