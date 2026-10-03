/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Scheduled.Defs

/-!
# Flat seed words for the scheduled recursive extractor

The initial field seed is followed by the fresh level seeds in increasing
order, then the final condenser and hash seeds. Each field element uses its
canonical coefficient word. Prefixes grow by appending the next level seed;
the full encoding groups the final appends as `(prefix ++ condenser) ++ hash`.

The total decoders split at these fixed widths. Inverse laws apply to words
of the exact stated length. These are semantic codecs, with no field
enumeration or runtime assertion.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Extractor

/-- Width of the initial field seed and the first `i` fresh level seeds. -/
def scheduledBlockSeedPrefixBits (n h Q E i : Nat) : Nat :=
  sparseFieldBits 1 (explicitCondenserBudget n (recursiveBlockEntropy h Q 0) E) +
    (Finset.range i).sum
      (recursiveBlockSeedWidth (scheduledBlockInitialWidth n h Q E) h Q E)

/-- Encode the initial seed followed by the executed fresh seeds in order. -/
noncomputable def encodeScheduledBlockSeedPrefix (n h Q E : Nat) :
    (i : Nat) → RecursiveSeeds (ScheduledInitialSeed n h Q E) (ScheduledLevelSeed n h Q E) i →
      List Bool
  | 0, seeds => BinaryFieldCodec.encode
      (sparseFieldExponent 1 (explicitCondenserBudget n (recursiveBlockEntropy h Q 0) E)) seeds
  | i + 1, seeds => encodeScheduledBlockSeedPrefix n h Q E i seeds.1 ++
      BinaryFieldCodec.encode (sparseFieldExponent 3 (explicitCondenserBudget
        (recursiveBlockWidth (scheduledBlockInitialWidth n h Q E) h Q E i)
        (recursiveBlockEntropy h Q i) E)) seeds.2

/-- Decode a prefix by splitting off its last fresh field word at the fixed prior width. -/
noncomputable def decodeScheduledBlockSeedPrefix (n h Q E : Nat) :
    (i : Nat) → List Bool →
      RecursiveSeeds (ScheduledInitialSeed n h Q E) (ScheduledLevelSeed n h Q E) i
  | 0, bits => BinaryFieldCodec.decode
      (sparseFieldExponent 1 (explicitCondenserBudget n (recursiveBlockEntropy h Q 0) E)) bits
  | i + 1, bits =>
      (decodeScheduledBlockSeedPrefix n h Q E i
        (bits.take (scheduledBlockSeedPrefixBits n h Q E i)),
       BinaryFieldCodec.decode (sparseFieldExponent 3 (explicitCondenserBudget
        (recursiveBlockWidth (scheduledBlockInitialWidth n h Q E) h Q E i)
        (recursiveBlockEntropy h Q i) E))
          (bits.drop (scheduledBlockSeedPrefixBits n h Q E i)))

/-- Encode the recursive seed prefix, final condenser seed, then final hash seed. -/
noncomputable def encodeScheduledBlockSeeds (n h Q E ell : Nat)
    (seeds : RecursiveSeeds (ScheduledInitialSeed n h Q E) (ScheduledLevelSeed n h Q E) h ×
      ScheduledFinalSeed n h Q E ell) : List Bool :=
  let width := recursiveBlockWidth (scheduledBlockInitialWidth n h Q E) h Q E h
  (encodeScheduledBlockSeedPrefix n h Q E h seeds.1 ++
    BinaryFieldCodec.encode (oneShotCondenserExponent width ell E) seeds.2.1) ++
      BinaryFieldCodec.encode (oneShotHashExponent width ell E) seeds.2.2

/-- Decode the recursive prefix and the two final field words at their fixed offsets. -/
noncomputable def decodeScheduledBlockSeeds (n h Q E ell : Nat) (bits : List Bool) :
    RecursiveSeeds (ScheduledInitialSeed n h Q E) (ScheduledLevelSeed n h Q E) h ×
      ScheduledFinalSeed n h Q E ell :=
  let width := recursiveBlockWidth (scheduledBlockInitialWidth n h Q E) h Q E h
  let prefixWidth := scheduledBlockSeedPrefixBits n h Q E h
  let finalCondenser := 2 * 3 ^ oneShotCondenserExponent width ell E
  (decodeScheduledBlockSeedPrefix n h Q E h (bits.take prefixWidth),
    (BinaryFieldCodec.decode (oneShotCondenserExponent width ell E)
      ((bits.drop prefixWidth).take finalCondenser),
     BinaryFieldCodec.decode (oneShotHashExponent width ell E)
      (bits.drop (prefixWidth + finalCondenser))))

end Algebraic.Cutwidth.Extractor
