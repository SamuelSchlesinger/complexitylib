/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Scheduled.Codec.Defs
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Scheduled.Codec.Internal

/-!
# Canonical seed-word equivalences for the scheduled extractor

One flat word contains the initial seed, fresh level seeds in increasing
order, and the final condenser and hash seeds. Prefix append laws and exact
widths expose the same layout to a runtime loop. The complete word has
exactly `scheduledBlockSeedBits` bits, and its codec is a bijection at that
length, including zero-depth schedules.

These are finite representation results built from `BinaryFieldCodec` and
list splitting. They need no enumeration instances and make no polynomial-time
claim about operations on abstract field elements or the complete recursion.
-/

public section

namespace Algebraic.Cutwidth.Extractor

/-- The zero-level prefix contains only the initial field seed. -/
theorem scheduledBlockSeedPrefixBits_zero (n h Q E : Nat) :
    scheduledBlockSeedPrefixBits n h Q E 0 =
      sparseFieldBits 1 (explicitCondenserBudget n (recursiveBlockEntropy h Q 0) E) :=
  Internal.scheduledBlockSeedPrefixBits_zero n h Q E

/-- A prefix grows by the exact field width of its next fresh seed. -/
theorem scheduledBlockSeedPrefixBits_succ (n h Q E i : Nat) :
    scheduledBlockSeedPrefixBits n h Q E (i + 1) =
      scheduledBlockSeedPrefixBits n h Q E i +
        recursiveBlockSeedWidth (scheduledBlockInitialWidth n h Q E) h Q E i :=
  Internal.scheduledBlockSeedPrefixBits_succ n h Q E i

/-- The full width consists of the recursive prefix and the final seed pair. -/
theorem scheduledBlockSeedBits_eq_prefix (n h Q E ell : Nat) :
    let width := recursiveBlockWidth (scheduledBlockInitialWidth n h Q E) h Q E h
    scheduledBlockSeedBits n h Q E ell = scheduledBlockSeedPrefixBits n h Q E h +
      (2 * 3 ^ oneShotCondenserExponent width ell E +
        2 * 3 ^ oneShotHashExponent width ell E) := rfl

/-- The zero-level encoding is the initial field's canonical word. -/
theorem encodeScheduledBlockSeedPrefix_zero (n h Q E : Nat)
    (seed : ScheduledInitialSeed n h Q E) :
    encodeScheduledBlockSeedPrefix n h Q E 0 seed = BinaryFieldCodec.encode
      (sparseFieldExponent 1 (explicitCondenserBudget n (recursiveBlockEntropy h Q 0) E)) seed :=
  rfl

/-- The next fresh seed is appended after all earlier seeds. -/
theorem encodeScheduledBlockSeedPrefix_succ (n h Q E i : Nat)
    (prior : RecursiveSeeds (ScheduledInitialSeed n h Q E) (ScheduledLevelSeed n h Q E) i)
    (fresh : ScheduledLevelSeed n h Q E i) :
    encodeScheduledBlockSeedPrefix n h Q E (i + 1) (prior, fresh) =
      encodeScheduledBlockSeedPrefix n h Q E i prior ++
        BinaryFieldCodec.encode (sparseFieldExponent 3 (explicitCondenserBudget
          (recursiveBlockWidth (scheduledBlockInitialWidth n h Q E) h Q E i)
          (recursiveBlockEntropy h Q i) E)) fresh := rfl

/-- Every prefix encoding has its prescribed initial-plus-level width. -/
theorem encodeScheduledBlockSeedPrefix_length (n h Q E i : Nat)
    (seeds : RecursiveSeeds (ScheduledInitialSeed n h Q E) (ScheduledLevelSeed n h Q E) i) :
    (encodeScheduledBlockSeedPrefix n h Q E i seeds).length =
      scheduledBlockSeedPrefixBits n h Q E i :=
  Internal.encodeScheduledBlockSeedPrefix_length n h Q E i seeds

/-- Decoding a canonical prefix recovers all its semantic field seeds. -/
theorem decode_encodeScheduledBlockSeedPrefix (n h Q E i : Nat)
    (seeds : RecursiveSeeds (ScheduledInitialSeed n h Q E) (ScheduledLevelSeed n h Q E) i) :
    decodeScheduledBlockSeedPrefix n h Q E i (encodeScheduledBlockSeedPrefix n h Q E i seeds) =
      seeds :=
  Internal.decode_encodeScheduledBlockSeedPrefix n h Q E i seeds

/-- Every word of the exact prefix width is recovered, including coefficient padding. -/
theorem encode_decodeScheduledBlockSeedPrefix (n h Q E i : Nat) (bits : List Bool)
    (length : bits.length = scheduledBlockSeedPrefixBits n h Q E i) :
    encodeScheduledBlockSeedPrefix n h Q E i (decodeScheduledBlockSeedPrefix n h Q E i bits) =
      bits :=
  Internal.encode_decodeScheduledBlockSeedPrefix n h Q E i bits length

/-- A recursive seed prefix is equivalent to one word of its exact width. -/
noncomputable def scheduledBlockSeedPrefixEquiv (n h Q E i : Nat) :
    RecursiveSeeds (ScheduledInitialSeed n h Q E) (ScheduledLevelSeed n h Q E) i ≃
      {bits : List Bool // bits.length = scheduledBlockSeedPrefixBits n h Q E i} where
  toFun seeds := ⟨encodeScheduledBlockSeedPrefix n h Q E i seeds,
    encodeScheduledBlockSeedPrefix_length n h Q E i seeds⟩
  invFun bits := decodeScheduledBlockSeedPrefix n h Q E i bits.val
  left_inv := decode_encodeScheduledBlockSeedPrefix n h Q E i
  right_inv bits := Subtype.ext (encode_decodeScheduledBlockSeedPrefix n h Q E i
    bits.val bits.property)

/-- The final words follow the prefix in condenser-then-hash order, with left grouping. -/
theorem encodeScheduledBlockSeeds_append (n h Q E ell : Nat)
    (seeds : RecursiveSeeds (ScheduledInitialSeed n h Q E) (ScheduledLevelSeed n h Q E) h ×
      ScheduledFinalSeed n h Q E ell) :
    let width := recursiveBlockWidth (scheduledBlockInitialWidth n h Q E) h Q E h
    encodeScheduledBlockSeeds n h Q E ell seeds =
      (encodeScheduledBlockSeedPrefix n h Q E h seeds.1 ++
        BinaryFieldCodec.encode (oneShotCondenserExponent width ell E) seeds.2.1) ++
          BinaryFieldCodec.encode (oneShotHashExponent width ell E) seeds.2.2 := rfl

/-- The flat seed word has exactly the previously specified complete seed budget. -/
theorem encodeScheduledBlockSeeds_length (n h Q E ell : Nat)
    (seeds : RecursiveSeeds (ScheduledInitialSeed n h Q E) (ScheduledLevelSeed n h Q E) h ×
      ScheduledFinalSeed n h Q E ell) :
    (encodeScheduledBlockSeeds n h Q E ell seeds).length = scheduledBlockSeedBits n h Q E ell :=
  Internal.encodeScheduledBlockSeeds_length n h Q E ell seeds

/-- The full decoder recovers every initial, internal, and final field seed. -/
theorem decode_encodeScheduledBlockSeeds (n h Q E ell : Nat)
    (seeds : RecursiveSeeds (ScheduledInitialSeed n h Q E) (ScheduledLevelSeed n h Q E) h ×
      ScheduledFinalSeed n h Q E ell) :
    decodeScheduledBlockSeeds n h Q E ell (encodeScheduledBlockSeeds n h Q E ell seeds) =
      seeds :=
  Internal.decode_encodeScheduledBlockSeeds n h Q E ell seeds

/-- Every word of the full prescribed length is its decoded tuple's exact encoding. -/
theorem encode_decodeScheduledBlockSeeds (n h Q E ell : Nat) (bits : List Bool)
    (length : bits.length = scheduledBlockSeedBits n h Q E ell) :
    encodeScheduledBlockSeeds n h Q E ell (decodeScheduledBlockSeeds n h Q E ell bits) =
      bits :=
  Internal.encode_decodeScheduledBlockSeeds n h Q E ell bits length

/-- The complete semantic seed tuple is equivalent to a flat word of the exact total width. -/
noncomputable def scheduledBlockSeedEquiv (n h Q E ell : Nat) :
    (RecursiveSeeds (ScheduledInitialSeed n h Q E) (ScheduledLevelSeed n h Q E) h ×
      ScheduledFinalSeed n h Q E ell) ≃
      {bits : List Bool // bits.length = scheduledBlockSeedBits n h Q E ell} where
  toFun seeds := ⟨encodeScheduledBlockSeeds n h Q E ell seeds,
    encodeScheduledBlockSeeds_length n h Q E ell seeds⟩
  invFun bits := decodeScheduledBlockSeeds n h Q E ell bits.val
  left_inv := decode_encodeScheduledBlockSeeds n h Q E ell
  right_inv bits := Subtype.ext (encode_decodeScheduledBlockSeeds n h Q E ell
    bits.val bits.property)

end Algebraic.Cutwidth.Extractor
