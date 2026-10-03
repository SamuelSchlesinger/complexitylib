/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.NearHalving.Codec.Defs
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.NearHalving.Codec.Internal

/-!
# Canonical seed words for the near-halving extractor

The initial `Unit` seed occupies the empty prefix. Each internal field seed
is appended in level order, followed by the final condenser and hash seeds.
The complete encoding is a bijection with words of exactly
`nearHalvingBlockSeedBits` bits, for all parameters including zero depth.

Lengths, append order, and both inverse laws need no enumeration instances.
The cardinality corollary accepts caller-supplied finite field instances.
These are semantic representation results; runtime evaluation is separate.
-/

public section

namespace Algebraic.Cutwidth.Extractor

/-- Identity initialization spends no random bits. -/
theorem nearHalvingBlockSeedPrefixBits_zero (n h Q E : Nat) :
    nearHalvingBlockSeedPrefixBits n h Q E 0 = 0 :=
  Internal.nearHalvingBlockSeedPrefixBits_zero n h Q E

/-- A prefix grows by the exact field width of its next fresh seed. -/
theorem nearHalvingBlockSeedPrefixBits_succ (n h Q E i : Nat) :
    nearHalvingBlockSeedPrefixBits n h Q E (i + 1) =
      nearHalvingBlockSeedPrefixBits n h Q E i + nearHalvingBlockSeedWidth n h Q E i :=
  Internal.nearHalvingBlockSeedPrefixBits_succ n h Q E i

/-- The full width consists of the recursive prefix and the final seed pair. -/
theorem nearHalvingBlockSeedBits_eq_prefix (n h Q E : Nat) :
    let width := nearHalvingBlockWidth n h Q E h
    let ell := nearHalvingBlockLeafLength h Q
    nearHalvingBlockSeedBits n h Q E = nearHalvingBlockSeedPrefixBits n h Q E h +
      (2 * 3 ^ oneShotCondenserExponent width ell E +
        2 * 3 ^ oneShotHashExponent width ell E) := rfl

/-- The trivial initial seed encodes as the empty word. -/
theorem encodeNearHalvingBlockSeedPrefix_zero (n h Q E : Nat) (seed : Unit) :
    encodeNearHalvingBlockSeedPrefix n h Q E 0 seed = [] := rfl

/-- The zero-level decoder always returns the trivial initial seed. -/
theorem decodeNearHalvingBlockSeedPrefix_zero (n h Q E : Nat) (bits : List Bool) :
    decodeNearHalvingBlockSeedPrefix n h Q E 0 bits = () := rfl

/-- The next fresh field word follows all earlier field words. -/
theorem encodeNearHalvingBlockSeedPrefix_succ (n h Q E i : Nat)
    (prior : RecursiveSeeds Unit (NearHalvingBlockLevelSeed n h Q E) i)
    (fresh : NearHalvingBlockLevelSeed n h Q E i) :
    encodeNearHalvingBlockSeedPrefix n h Q E (i + 1) (prior, fresh) =
      encodeNearHalvingBlockSeedPrefix n h Q E i prior ++
        BinaryFieldCodec.encode (sparseFieldExponent (nearHalvingBlockRate h)
          (explicitCondenserBudget (nearHalvingBlockWidth n h Q E i)
            (nearHalvingBlockEntropy h Q i) E)) fresh := rfl

/-- Every prefix encoding has the prescribed sum of fresh field widths. -/
theorem encodeNearHalvingBlockSeedPrefix_length (n h Q E i : Nat)
    (seeds : RecursiveSeeds Unit (NearHalvingBlockLevelSeed n h Q E) i) :
    (encodeNearHalvingBlockSeedPrefix n h Q E i seeds).length =
      nearHalvingBlockSeedPrefixBits n h Q E i :=
  Internal.encodeNearHalvingBlockSeedPrefix_length n h Q E i seeds

/-- Decoding a canonical prefix recovers every retained seed. -/
theorem decode_encodeNearHalvingBlockSeedPrefix (n h Q E i : Nat)
    (seeds : RecursiveSeeds Unit (NearHalvingBlockLevelSeed n h Q E) i) :
    decodeNearHalvingBlockSeedPrefix n h Q E i
      (encodeNearHalvingBlockSeedPrefix n h Q E i seeds) = seeds :=
  Internal.decode_encodeNearHalvingBlockSeedPrefix n h Q E i seeds

/-- Every word of the exact prefix width is recovered, preserving all coefficient zeros. -/
theorem encode_decodeNearHalvingBlockSeedPrefix (n h Q E i : Nat) (bits : List Bool)
    (length : bits.length = nearHalvingBlockSeedPrefixBits n h Q E i) :
    encodeNearHalvingBlockSeedPrefix n h Q E i
      (decodeNearHalvingBlockSeedPrefix n h Q E i bits) = bits :=
  Internal.encode_decodeNearHalvingBlockSeedPrefix n h Q E i bits length

/-- A retained seed prefix is equivalent to one Boolean word of its exact width. -/
noncomputable def nearHalvingBlockSeedPrefixEquiv (n h Q E i : Nat) :
    RecursiveSeeds Unit (NearHalvingBlockLevelSeed n h Q E) i ≃
      {bits : List Bool // bits.length = nearHalvingBlockSeedPrefixBits n h Q E i} where
  toFun seeds := ⟨encodeNearHalvingBlockSeedPrefix n h Q E i seeds,
    encodeNearHalvingBlockSeedPrefix_length n h Q E i seeds⟩
  invFun bits := decodeNearHalvingBlockSeedPrefix n h Q E i bits.val
  left_inv := decode_encodeNearHalvingBlockSeedPrefix n h Q E i
  right_inv bits := Subtype.ext
    (encode_decodeNearHalvingBlockSeedPrefix n h Q E i bits.val bits.property)

/-- Final words follow the prefix in condenser-then-hash order, with left grouping. -/
theorem encodeNearHalvingBlockSeeds_append (n h Q E : Nat)
    (seeds : NearHalvingBlockSeeds n h Q E) :
    let width := nearHalvingBlockWidth n h Q E h
    let ell := nearHalvingBlockLeafLength h Q
    encodeNearHalvingBlockSeeds n h Q E seeds =
      (encodeNearHalvingBlockSeedPrefix n h Q E h seeds.1 ++
        BinaryFieldCodec.encode (oneShotCondenserExponent width ell E) seeds.2.1) ++
          BinaryFieldCodec.encode (oneShotHashExponent width ell E) seeds.2.2 := rfl

/-- The encoded word has exactly the complete near-halving seed budget. -/
theorem encodeNearHalvingBlockSeeds_length (n h Q E : Nat)
    (seeds : NearHalvingBlockSeeds n h Q E) :
    (encodeNearHalvingBlockSeeds n h Q E seeds).length = nearHalvingBlockSeedBits n h Q E :=
  Internal.encodeNearHalvingBlockSeeds_length n h Q E seeds

/-- The full decoder recovers every internal and final field seed. -/
theorem decode_encodeNearHalvingBlockSeeds (n h Q E : Nat)
    (seeds : NearHalvingBlockSeeds n h Q E) :
    decodeNearHalvingBlockSeeds n h Q E (encodeNearHalvingBlockSeeds n h Q E seeds) =
      seeds :=
  Internal.decode_encodeNearHalvingBlockSeeds n h Q E seeds

/-- Every word of the full prescribed length is its decoded tuple's exact encoding. -/
theorem encode_decodeNearHalvingBlockSeeds (n h Q E : Nat) (bits : List Bool)
    (length : bits.length = nearHalvingBlockSeedBits n h Q E) :
    encodeNearHalvingBlockSeeds n h Q E (decodeNearHalvingBlockSeeds n h Q E bits) =
      bits :=
  Internal.encode_decodeNearHalvingBlockSeeds n h Q E bits length

/-- The semantic seed tuple is equivalent to a word of the exact total bit width. -/
noncomputable def nearHalvingBlockSeedEquiv (n h Q E : Nat) :
    NearHalvingBlockSeeds n h Q E ≃
      {bits : List Bool // bits.length = nearHalvingBlockSeedBits n h Q E} where
  toFun seeds := ⟨encodeNearHalvingBlockSeeds n h Q E seeds,
    encodeNearHalvingBlockSeeds_length n h Q E seeds⟩
  invFun bits := decodeNearHalvingBlockSeeds n h Q E bits.val
  left_inv := decode_encodeNearHalvingBlockSeeds n h Q E
  right_inv bits := Subtype.ext
    (encode_decodeNearHalvingBlockSeeds n h Q E bits.val bits.property)

/-- The forward seed equivalence is the canonical ordered encoding. -/
theorem nearHalvingBlockSeedEquiv_apply (n h Q E : Nat)
    (seeds : NearHalvingBlockSeeds n h Q E) :
    (nearHalvingBlockSeedEquiv n h Q E seeds).val = encodeNearHalvingBlockSeeds n h Q E seeds := by
  simp only [nearHalvingBlockSeedEquiv, Equiv.coe_fn_mk]

/-- The inverse seed equivalence is the total decoder restricted to words of the exact width. -/
theorem nearHalvingBlockSeedEquiv_symm_apply (n h Q E : Nat)
    (bits : {bits : List Bool // bits.length = nearHalvingBlockSeedBits n h Q E}) :
    (nearHalvingBlockSeedEquiv n h Q E).symm bits = decodeNearHalvingBlockSeeds n h Q E bits.val := by
  simp only [nearHalvingBlockSeedEquiv, Equiv.coe_fn_symm_mk]

/-- The exact number of semantic seeds is the power of two specified by their bit budget. -/
theorem card_nearHalvingBlockSeeds (n h Q E : Nat)
    [∀ s, Fintype (AdjoinRoot (binaryModulus s))] :
    Fintype.card (NearHalvingBlockSeeds n h Q E) = 2 ^ nearHalvingBlockSeedBits n h Q E :=
  Internal.card_nearHalvingBlockSeeds n h Q E

end Algebraic.Cutwidth.Extractor
