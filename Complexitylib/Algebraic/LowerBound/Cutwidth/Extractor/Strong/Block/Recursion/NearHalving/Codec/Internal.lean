/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.NearHalving.Codec.Defs
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Modulus.Binary.Codec
import Mathlib.Data.List.TakeDrop
import Mathlib.Data.Vector.Basic

/-!
# Exact widths and inverse laws for near-halving seed words

The prefix induction starts at the empty word and appends one canonical
field word at each level. The final two fields use the same fixed-width
splitting. The resulting equivalence with Boolean words also gives the
exact cardinality, without any field enumeration in the codec.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

theorem nearHalvingBlockSeedPrefixBits_zero (n h Q E : Nat) :
    nearHalvingBlockSeedPrefixBits n h Q E 0 = 0 := by
  simp only [nearHalvingBlockSeedPrefixBits, Finset.range_zero, Finset.sum_empty]

theorem nearHalvingBlockSeedPrefixBits_succ (n h Q E i : Nat) :
    nearHalvingBlockSeedPrefixBits n h Q E (i + 1) =
      nearHalvingBlockSeedPrefixBits n h Q E i + nearHalvingBlockSeedWidth n h Q E i := by
  simp only [nearHalvingBlockSeedPrefixBits, Finset.sum_range_succ]

theorem encodeNearHalvingBlockSeedPrefix_length (n h Q E i : Nat)
    (seeds : RecursiveSeeds Unit (NearHalvingBlockLevelSeed n h Q E) i) :
    (encodeNearHalvingBlockSeedPrefix n h Q E i seeds).length =
      nearHalvingBlockSeedPrefixBits n h Q E i := by
  induction i with
  | zero =>
    rw [nearHalvingBlockSeedPrefixBits_zero]
    rfl
  | succ i ih =>
    rw [encodeNearHalvingBlockSeedPrefix, List.length_append, ih,
      BinaryFieldCodec.length_encode, nearHalvingBlockSeedPrefixBits_succ]
    rfl

theorem decode_encodeNearHalvingBlockSeedPrefix (n h Q E i : Nat)
    (seeds : RecursiveSeeds Unit (NearHalvingBlockLevelSeed n h Q E) i) :
    decodeNearHalvingBlockSeedPrefix n h Q E i
      (encodeNearHalvingBlockSeedPrefix n h Q E i seeds) = seeds := by
  induction i with
  | zero => cases seeds; rfl
  | succ i ih =>
    rcases seeds with ⟨prior, fresh⟩
    simp only [encodeNearHalvingBlockSeedPrefix, decodeNearHalvingBlockSeedPrefix]
    rw [← encodeNearHalvingBlockSeedPrefix_length n h Q E i prior, List.take_left,
      List.drop_left, ih, BinaryFieldCodec.decode_encode]

theorem encode_decodeNearHalvingBlockSeedPrefix (n h Q E i : Nat) (bits : List Bool)
    (length : bits.length = nearHalvingBlockSeedPrefixBits n h Q E i) :
    encodeNearHalvingBlockSeedPrefix n h Q E i
      (decodeNearHalvingBlockSeedPrefix n h Q E i bits) = bits := by
  induction i generalizing bits with
  | zero =>
    rw [nearHalvingBlockSeedPrefixBits_zero] at length
    exact (List.length_eq_zero_iff.mp length).symm
  | succ i ih =>
    have total := length
    rw [nearHalvingBlockSeedPrefixBits_succ] at total
    have first : (bits.take (nearHalvingBlockSeedPrefixBits n h Q E i)).length =
        nearHalvingBlockSeedPrefixBits n h Q E i := by
      rw [List.length_take]
      exact min_eq_left (by lia)
    have last : (bits.drop (nearHalvingBlockSeedPrefixBits n h Q E i)).length =
        nearHalvingBlockSeedWidth n h Q E i := by
      rw [List.length_drop]
      lia
    simp only [encodeNearHalvingBlockSeedPrefix, decodeNearHalvingBlockSeedPrefix]
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

theorem encodeNearHalvingBlockSeeds_length (n h Q E : Nat)
    (seeds : NearHalvingBlockSeeds n h Q E) :
    (encodeNearHalvingBlockSeeds n h Q E seeds).length = nearHalvingBlockSeedBits n h Q E := by
  simp only [encodeNearHalvingBlockSeeds, List.length_append,
    encodeNearHalvingBlockSeedPrefix_length, BinaryFieldCodec.length_encode,
    nearHalvingBlockSeedBits, nearHalvingBlockSeedPrefixBits, Nat.add_assoc]

theorem decode_encodeNearHalvingBlockSeeds (n h Q E : Nat)
    (seeds : NearHalvingBlockSeeds n h Q E) :
    decodeNearHalvingBlockSeeds n h Q E (encodeNearHalvingBlockSeeds n h Q E seeds) =
      seeds := by
  simp only [decodeNearHalvingBlockSeeds, encodeNearHalvingBlockSeeds]
  rw [← encodeNearHalvingBlockSeedPrefix_length n h Q E h seeds.1,
    ← BinaryFieldCodec.length_encode
      (oneShotCondenserExponent (nearHalvingBlockWidth n h Q E h)
        (nearHalvingBlockLeafLength h Q) E) seeds.2.1,
    take_three_first, take_three_second, drop_three_last,
    decode_encodeNearHalvingBlockSeedPrefix, BinaryFieldCodec.decode_encode,
    BinaryFieldCodec.decode_encode]

theorem encode_decodeNearHalvingBlockSeeds (n h Q E : Nat) (bits : List Bool)
    (length : bits.length = nearHalvingBlockSeedBits n h Q E) :
    encodeNearHalvingBlockSeeds n h Q E (decodeNearHalvingBlockSeeds n h Q E bits) =
      bits := by
  let width := nearHalvingBlockWidth n h Q E h
  let ell := nearHalvingBlockLeafLength h Q
  let p := nearHalvingBlockSeedPrefixBits n h Q E h
  let c := 2 * 3 ^ oneShotCondenserExponent width ell E
  let d := 2 * 3 ^ oneShotHashExponent width ell E
  have total : bits.length = p + c + d := by
    simpa only [p, c, d, width, ell, nearHalvingBlockSeedBits,
      nearHalvingBlockSeedPrefixBits, Nat.add_assoc] using length
  have first : (bits.take p).length = p := by
    rw [List.length_take]
    exact min_eq_left (by lia)
  have second : ((bits.drop p).take c).length = c := by
    rw [List.length_take, List.length_drop]
    exact min_eq_left (by lia)
  have last : (bits.drop (p + c)).length = d := by
    rw [List.length_drop]
    lia
  simp only [encodeNearHalvingBlockSeeds, decodeNearHalvingBlockSeeds]
  rw [encode_decodeNearHalvingBlockSeedPrefix _ _ _ _ _ _ first,
    BinaryFieldCodec.encode_decode _ _ second, BinaryFieldCodec.encode_decode _ _ last,
    List.append_assoc, List.drop_take_append_drop, List.take_append_drop]

theorem card_nearHalvingBlockSeeds (n h Q E : Nat)
    [∀ s, Fintype (AdjoinRoot (binaryModulus s))] :
    Fintype.card (NearHalvingBlockSeeds n h Q E) = 2 ^ nearHalvingBlockSeedBits n h Q E := by
  let encoded : NearHalvingBlockSeeds n h Q E ≃
      {bits : List Bool // bits.length = nearHalvingBlockSeedBits n h Q E} :=
    { toFun seeds := ⟨encodeNearHalvingBlockSeeds n h Q E seeds,
        encodeNearHalvingBlockSeeds_length n h Q E seeds⟩
      invFun bits := decodeNearHalvingBlockSeeds n h Q E bits.val
      left_inv := decode_encodeNearHalvingBlockSeeds n h Q E
      right_inv bits := Subtype.ext
        (encode_decodeNearHalvingBlockSeeds n h Q E bits.val bits.property) }
  have card := Fintype.card_congr (encoded.trans (Equiv.vectorEquivFin Bool _))
  simpa only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] using card

end Algebraic.Cutwidth.Extractor.Internal
