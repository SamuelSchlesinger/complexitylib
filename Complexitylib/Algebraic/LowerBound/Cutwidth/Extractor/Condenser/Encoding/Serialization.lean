/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Encoding.Serialization.Defs
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Encoding.Correctness.Defs
public import Complexitylib.Encoding.BitPolynomial.Addition.Defs
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Encoding.Serialization.Internal

/-!
# Exact serialization of statistical condenser outputs

The coordinate vector and its concatenated fixed-width bit representation
are equivalent, including the empty vector. Serialization is injective
independently of any source distribution, and decoding preserves each
coordinate's position and every padding bit at the canonical total width.
Coordinate addition corresponds exactly to padded bitwise XOR.

Re-encoding the decoded runtime output returns its exact original bits.
This links statistical statements about field-coordinate vectors to the
existing bit output, using only the correct base-field width. The codec
operations are semantic maps; the runtime algorithm and its cost are
already supplied by `Encoding`.
-/

public section

namespace Algebraic.Cutwidth.Extractor

/-- Serialization writes one canonical-width block for every coordinate. -/
theorem encodeCondenserOutput_length (s m : Nat)
    (coords : Fin m → AdjoinRoot (binaryModulus s)) :
    (encodeCondenserOutput s m coords).length = m * (2 * 3 ^ s) :=
  Internal.encodeCondenserOutput_length s m coords

/-- Each consecutive output block is exactly the corresponding field encoding. -/
theorem coefficientBlock_encodeCondenserOutput (s m : Nat)
    (coords : Fin m → AdjoinRoot (binaryModulus s)) (i : Fin m) :
    Complexity.BitPolynomial.coefficientBlock (encodeCondenserOutput s m coords)
        (2 * 3 ^ s) i.val = BinaryFieldCodec.encode s (coords i) :=
  Internal.coefficientBlock_encodeCondenserOutput s m coords i

/-- Decoding after serialization recovers every coordinate vector. -/
theorem decode_encodeCondenserOutput (s m : Nat)
    (coords : Fin m → AdjoinRoot (binaryModulus s)) :
    decodeCondenserOutput s m (encodeCondenserOutput s m coords) = coords :=
  Internal.decode_encodeCondenserOutput s m coords

/-- A bitstring of the exact total width is recovered, including all zero padding. -/
theorem encode_decodeCondenserOutput (s m : Nat) (bits : List Bool)
    (length : bits.length = m * (2 * 3 ^ s)) :
    encodeCondenserOutput s m (decodeCondenserOutput s m bits) = bits :=
  Internal.encode_decodeCondenserOutput s m bits length

/-- Distinct coordinate vectors always have distinct serialized words. -/
theorem encodeCondenserOutput_injective (s m : Nat) :
    Function.Injective (encodeCondenserOutput s m) :=
  Internal.encodeCondenserOutput_injective s m

/-- Decoding preserves padded XOR, including words of unequal lengths. -/
theorem decodeCondenserOutput_addBits (s m : Nat) (a b : List Bool) :
    decodeCondenserOutput s m (Complexity.BitPolynomial.addBits a b) =
      decodeCondenserOutput s m a + decodeCondenserOutput s m b :=
  Internal.decodeCondenserOutput_addBits s m a b

/-- Serialization sends coordinate addition to XOR of the two fixed-width words. -/
theorem encodeCondenserOutput_add (s m : Nat)
    (a b : Fin m → AdjoinRoot (binaryModulus s)) :
    encodeCondenserOutput s m (a + b) =
      Complexity.BitPolynomial.addBits (encodeCondenserOutput s m a)
        (encodeCondenserOutput s m b) :=
  Internal.encodeCondenserOutput_add s m a b

/-- Coordinate vectors correspond exactly to bitstrings of the prescribed total width. -/
noncomputable def condenserOutputEquiv (s m : Nat) :
    (Fin m → AdjoinRoot (binaryModulus s)) ≃
      {bits : List Bool // bits.length = m * (2 * 3 ^ s)} where
  toFun coords := ⟨encodeCondenserOutput s m coords, encodeCondenserOutput_length s m coords⟩
  invFun bits := decodeCondenserOutput s m bits.val
  left_inv := decode_encodeCondenserOutput s m
  right_inv bits := Subtype.ext (encode_decodeCondenserOutput s m bits.val bits.property)

/-- The serialized statistical output is the actual runtime bit output.
Only the base-field width is required; extension and iteration words remain arbitrary. -/
theorem encodeCondenserOutput_decodedCondenser (s : Nat)
    (halfDegree extensionCount stride count bits : List Bool)
    (seed : AdjoinRoot (binaryModulus s)) (half : halfDegree.length = 3 ^ s) :
    encodeCondenserOutput s count.length
        (decodedCondenser s halfDegree extensionCount stride count bits seed) =
      condenserBits bits halfDegree extensionCount (BinaryFieldCodec.encode s seed) stride count :=
  Internal.encodeCondenserOutput_decodedCondenser s halfDegree extensionCount stride count bits
    seed half

end Algebraic.Cutwidth.Extractor
