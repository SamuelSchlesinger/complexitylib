/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Encoding.Correctness.Defs
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Encoding.Correctness.Internal.Packing
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Modulus.Binary.Codec
import Complexitylib.Encoding.BitPolynomial.Transpose

/-!
# Fixed-length sources embed injectively into coefficient polynomials

Packing transposes the coefficient rectangle into a canonical-width binary
quotient representation. Equal source polynomials therefore have equal
packed words by the quotient codec's inverse law. Two transposes recover
the source padded to the full rectangle, and a common original length
recovers the unpadded words. The permitted length can be any value up to
the rectangle's capacity, including zero.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

open Complexity.BitPolynomial

private theorem eq_of_padded_eq (n width : Nat) (capacity : n ≤ width)
    (a b : List Bool) (ha : a.length = n) (hb : b.length = n)
    (same : (List.range width).map (fun k => a[k]?.getD false) =
      (List.range width).map (fun k => b[k]?.getD false)) : a = b := by
  apply List.ext_getElem (ha.trans hb.symm)
  intro k ka kb
  have bound : k < width := by lia
  have entry := congrArg (fun bits : List Bool => bits[k]?.getD false) same
  simpa only [List.getElem?_map, List.getElem?_range bound, Option.map_some,
    Option.getD_some, List.getElem?_eq_getElem ka, List.getElem?_eq_getElem kb] using entry

theorem sourcePolynomial_inj_of_length (s v n : Nat)
    (capacity : n ≤ (2 * 3 ^ s) * 3 ^ v) (a b : List Bool)
    (ha : a.length = n) (hb : b.length = n)
    (same : sourcePolynomial s (3 ^ v) a = sourcePolynomial s (3 ^ v) b) : a = b := by
  have decoded :
      BinaryFieldCodec.decode (s + v) (transposeBits (3 ^ v) (2 * 3 ^ s) a) =
        BinaryFieldCodec.decode (s + v) (transposeBits (3 ^ v) (2 * 3 ^ s) b) := by
    apply (binaryExtensionEquiv s v).injective
    rw [binaryExtensionEquiv_decode_transpose, binaryExtensionEquiv_decode_transpose, same]
  have width (bits : List Bool) :
      (transposeBits (3 ^ v) (2 * 3 ^ s) bits).length = 2 * 3 ^ (s + v) := by
    rw [transposeBits_length, pow_add]
    ac_rfl
  have packed := congrArg (BinaryFieldCodec.encode (s + v)) decoded
  rw [BinaryFieldCodec.encode_decode _ _ (width a),
    BinaryFieldCodec.encode_decode _ _ (width b)] at packed
  have padded := congrArg (transposeBits (2 * 3 ^ s) (3 ^ v)) packed
  rw [transposeBits_transposeBits, transposeBits_transposeBits] at padded
  exact eq_of_padded_eq n ((3 ^ v) * (2 * 3 ^ s))
    (by simpa only [Nat.mul_comm] using capacity) a b ha hb padded

theorem sourcePolynomial_injectiveOn_length (s v n : Nat)
    (capacity : n ≤ (2 * 3 ^ s) * 3 ^ v) :
    Set.InjOn (sourcePolynomial s (3 ^ v)) {bits | bits.length = n} := by
  intro a ha b hb same
  exact sourcePolynomial_inj_of_length s v n capacity a b ha hb same

end Algebraic.Cutwidth.Extractor.Internal
