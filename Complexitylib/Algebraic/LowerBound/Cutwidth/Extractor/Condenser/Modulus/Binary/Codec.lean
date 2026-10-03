/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Modulus.Binary.Codec.Defs
public import Complexitylib.Encoding.BitPolynomial.Addition.Defs
public import Complexitylib.Encoding.BitPolynomial.Frobenius.Defs
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Modulus.Binary.Codec.Internal

/-!
# The fixed-width binary quotient codec

Every quotient element has exactly one representation of length `2 * 3^s`.
Decoding is polynomial interpretation followed by the quotient map; encoding
uses Mathlib's unique monic remainder. Arbitrary input lists may include
padding or higher powers, while the encoding always has canonical width.

The representation proof uses `AdjoinRoot.modByMonicHom` and its inverse law:
https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/AdjoinRoot.html.
This semantic equivalence is separate from any encoded evaluator or FP claim.
-/

public section

namespace Algebraic.Cutwidth.Extractor.BinaryFieldCodec

/-- Encoding retains exactly the modulus degree in coefficient bits. -/
theorem length_encode (s : Nat) (x : AdjoinRoot (binaryModulus s)) :
    (encode s x).length = 2 * 3 ^ s :=
  Internal.length_encode s x

/-- The encoded polynomial is exactly the unique monic remainder. -/
theorem ofBits_encode (s : Nat) (x : AdjoinRoot (binaryModulus s)) :
    Complexity.BitPolynomial.ofBits (encode s x) =
      AdjoinRoot.modByMonicHom (binaryModulus_monic s) x :=
  Internal.ofBits_encode s x

/-- Encoding and decoding recover every semantic quotient element. -/
theorem decode_encode (s : Nat) (x : AdjoinRoot (binaryModulus s)) :
    decode s (encode s x) = x :=
  Internal.decode_encode s x

/-- Every list of the canonical width is recovered exactly, including high zeros. -/
theorem encode_decode (s : Nat) (bits : List Bool) (length : bits.length = 2 * 3 ^ s) :
    encode s (decode s bits) = bits :=
  Internal.encode_decode s bits length

/-- Quotient elements correspond exactly to coefficient lists of the modulus degree. -/
noncomputable def equiv (s : Nat) : AdjoinRoot (binaryModulus s) ≃ Bits s where
  toFun x := ⟨encode s x, length_encode s x⟩
  invFun bits := decode s bits.val
  left_inv := decode_encode s
  right_inv bits := Subtype.ext (encode_decode s bits.val bits.property)

/-- Bitwise polynomial addition decodes to quotient addition. -/
theorem decode_addBits (s : Nat) (a b : List Bool) :
    decode s (Complexity.BitPolynomial.addBits a b) = decode s a + decode s b :=
  Internal.decode_addBits s a b

/-- Carryless polynomial multiplication decodes to quotient multiplication. -/
theorem decode_mulBits (s : Nat) (a b : List Bool) :
    decode s (Complexity.BitPolynomial.mulBits a b) = decode s a * decode s b :=
  Internal.decode_mulBits s a b

/-- Reducing by any bit representation of the modulus preserves the quotient class. -/
theorem decode_remainderBits (s : Nat) (a modulus : List Bool)
    (represents : Complexity.BitPolynomial.ofBits modulus = binaryModulus s) :
    decode s (Complexity.BitPolynomial.remainderBits a modulus) = decode s a :=
  Internal.decode_remainderBits s a modulus represents

/-- The bounded modular-squaring algorithm decodes to the corresponding power
in the quotient, for every supplied representation of the binary modulus. -/
theorem decode_frobeniusBits (s : Nat) (a modulus count : List Bool)
    (represents : Complexity.BitPolynomial.ofBits modulus = binaryModulus s) :
    decode s (Complexity.BitPolynomial.frobeniusBits a modulus count) =
      decode s a ^ (2 ^ count.length) :=
  Internal.decode_frobeniusBits s a modulus count represents

end Algebraic.Cutwidth.Extractor.BinaryFieldCodec
