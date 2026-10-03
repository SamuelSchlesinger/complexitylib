/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Scheduled.Codec.Defs
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Modulus.Binary.Codec
import Mathlib.Data.List.TakeDrop

/-!
# Exact widths and inverse laws for scheduled seed words

The prefix induction appends one canonical field word at each level.
Taking and dropping at its prior width recover both components. The final
condenser and hash words use the same fixed-width decomposition, preserving
all coefficient zeros without enumerating any quotient field.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

theorem scheduledBlockSeedPrefixBits_zero (n h Q E : Nat) :
    scheduledBlockSeedPrefixBits n h Q E 0 =
      sparseFieldBits 1 (explicitCondenserBudget n (recursiveBlockEntropy h Q 0) E) := by
  simp only [scheduledBlockSeedPrefixBits, Finset.range_zero, Finset.sum_empty, Nat.add_zero]

theorem scheduledBlockSeedPrefixBits_succ (n h Q E i : Nat) :
    scheduledBlockSeedPrefixBits n h Q E (i + 1) =
      scheduledBlockSeedPrefixBits n h Q E i +
        recursiveBlockSeedWidth (scheduledBlockInitialWidth n h Q E) h Q E i := by
  simp only [scheduledBlockSeedPrefixBits, Finset.sum_range_succ, Nat.add_assoc]

theorem encodeScheduledBlockSeedPrefix_length (n h Q E i : Nat)
    (seeds : RecursiveSeeds (ScheduledInitialSeed n h Q E) (ScheduledLevelSeed n h Q E) i) :
    (encodeScheduledBlockSeedPrefix n h Q E i seeds).length =
      scheduledBlockSeedPrefixBits n h Q E i := by
  induction i with
  | zero =>
    simpa only [encodeScheduledBlockSeedPrefix, scheduledBlockSeedPrefixBits_zero,
      sparseFieldBits] using BinaryFieldCodec.length_encode _ seeds
  | succ i ih =>
    rw [encodeScheduledBlockSeedPrefix, List.length_append, ih, BinaryFieldCodec.length_encode,
      scheduledBlockSeedPrefixBits_succ]
    rfl

theorem decode_encodeScheduledBlockSeedPrefix (n h Q E i : Nat)
    (seeds : RecursiveSeeds (ScheduledInitialSeed n h Q E) (ScheduledLevelSeed n h Q E) i) :
    decodeScheduledBlockSeedPrefix n h Q E i (encodeScheduledBlockSeedPrefix n h Q E i seeds) =
      seeds := by
  induction i with
  | zero => exact BinaryFieldCodec.decode_encode _ seeds
  | succ i ih =>
    rcases seeds with ⟨prior, fresh⟩
    simp only [encodeScheduledBlockSeedPrefix, decodeScheduledBlockSeedPrefix]
    rw [← encodeScheduledBlockSeedPrefix_length n h Q E i prior, List.take_left,
      List.drop_left, ih, BinaryFieldCodec.decode_encode]

theorem encode_decodeScheduledBlockSeedPrefix (n h Q E i : Nat) (bits : List Bool)
    (length : bits.length = scheduledBlockSeedPrefixBits n h Q E i) :
    encodeScheduledBlockSeedPrefix n h Q E i (decodeScheduledBlockSeedPrefix n h Q E i bits) =
      bits := by
  induction i generalizing bits with
  | zero =>
    exact BinaryFieldCodec.encode_decode _ bits (by
      simpa only [scheduledBlockSeedPrefixBits_zero, sparseFieldBits] using length)
  | succ i ih =>
    have total := length
    rw [scheduledBlockSeedPrefixBits_succ] at total
    have first : (bits.take (scheduledBlockSeedPrefixBits n h Q E i)).length =
        scheduledBlockSeedPrefixBits n h Q E i := by
      rw [List.length_take]
      exact min_eq_left (by lia)
    have last : (bits.drop (scheduledBlockSeedPrefixBits n h Q E i)).length =
        recursiveBlockSeedWidth (scheduledBlockInitialWidth n h Q E) h Q E i := by
      rw [List.length_drop]
      lia
    simp only [encodeScheduledBlockSeedPrefix, decodeScheduledBlockSeedPrefix]
    rw [ih _ first, BinaryFieldCodec.encode_decode _ _ last, List.take_append_drop]

private theorem take_three_first (a b c : List Bool) :
    ((a ++ b) ++ c).take a.length = a := by
  rw [List.append_assoc, List.take_left]

private theorem take_three_second (a b c : List Bool) :
    (((a ++ b) ++ c).drop a.length).take b.length = b := by
  rw [List.append_assoc, List.drop_left, List.take_left]

private theorem drop_three_last (a b c : List Bool) :
    ((a ++ b) ++ c).drop (a.length + b.length) = c := by
  simpa only [List.length_append] using (List.drop_left (l₁ := a ++ b) (l₂ := c))

theorem encodeScheduledBlockSeeds_length (n h Q E ell : Nat)
    (seeds : RecursiveSeeds (ScheduledInitialSeed n h Q E) (ScheduledLevelSeed n h Q E) h ×
      ScheduledFinalSeed n h Q E ell) :
    (encodeScheduledBlockSeeds n h Q E ell seeds).length = scheduledBlockSeedBits n h Q E ell := by
  simp only [encodeScheduledBlockSeeds, List.length_append, encodeScheduledBlockSeedPrefix_length,
    BinaryFieldCodec.length_encode, scheduledBlockSeedBits, scheduledBlockSeedPrefixBits,
    Nat.add_assoc]

theorem decode_encodeScheduledBlockSeeds (n h Q E ell : Nat)
    (seeds : RecursiveSeeds (ScheduledInitialSeed n h Q E) (ScheduledLevelSeed n h Q E) h ×
      ScheduledFinalSeed n h Q E ell) :
    decodeScheduledBlockSeeds n h Q E ell (encodeScheduledBlockSeeds n h Q E ell seeds) =
      seeds := by
  simp only [decodeScheduledBlockSeeds, encodeScheduledBlockSeeds]
  rw [← encodeScheduledBlockSeedPrefix_length n h Q E h seeds.1,
    ← BinaryFieldCodec.length_encode
      (oneShotCondenserExponent
        (recursiveBlockWidth (scheduledBlockInitialWidth n h Q E) h Q E h) ell E) seeds.2.1,
    take_three_first, take_three_second, drop_three_last,
    decode_encodeScheduledBlockSeedPrefix, BinaryFieldCodec.decode_encode,
    BinaryFieldCodec.decode_encode]

theorem encode_decodeScheduledBlockSeeds (n h Q E ell : Nat) (bits : List Bool)
    (length : bits.length = scheduledBlockSeedBits n h Q E ell) :
    encodeScheduledBlockSeeds n h Q E ell (decodeScheduledBlockSeeds n h Q E ell bits) =
      bits := by
  let width := recursiveBlockWidth (scheduledBlockInitialWidth n h Q E) h Q E h
  let p := scheduledBlockSeedPrefixBits n h Q E h
  let c := 2 * 3 ^ oneShotCondenserExponent width ell E
  let d := 2 * 3 ^ oneShotHashExponent width ell E
  have total : bits.length = p + c + d := by
    simpa only [p, c, d, width, scheduledBlockSeedBits, scheduledBlockSeedPrefixBits,
      Nat.add_assoc] using length
  have first : (bits.take p).length = p := by
    rw [List.length_take]
    exact min_eq_left (by lia)
  have second : ((bits.drop p).take c).length = c := by
    rw [List.length_take, List.length_drop]
    exact min_eq_left (by lia)
  have last : (bits.drop (p + c)).length = d := by
    rw [List.length_drop]
    lia
  simp only [encodeScheduledBlockSeeds, decodeScheduledBlockSeeds]
  rw [encode_decodeScheduledBlockSeedPrefix _ _ _ _ _ _ first,
    BinaryFieldCodec.encode_decode _ _ second, BinaryFieldCodec.encode_decode _ _ last,
    List.append_assoc, List.drop_take_append_drop, List.take_append_drop]

end Algebraic.Cutwidth.Extractor.Internal
