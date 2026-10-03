/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Encoding.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Encoding.Correctness.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Modulus.Binary.Extension.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Polynomial.Defs
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Encoding.Correctness.Internal.Basic
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Encoding.Correctness.Internal.Packing
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Encoding.Correctness.Internal.Horner
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Modulus.Binary.Codec
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Modulus.Binary.Encoding
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Polynomial
import Complexitylib.Encoding.BitPolynomial.Transpose
import Mathlib.Tactic.Ring

/-!
# The packed binary powering program computes extension-field Frobenius

Packing transports source coefficients into the larger binary quotient.
After bounded modular squaring, inverse transposition recovers a polynomial
of degree below the extension modulus. Its quotient class is the required
power, so uniqueness of monic remainder identifies the entire polynomial.
Horner evaluation then gives the actual condenser coordinate.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

open Complexity.BitPolynomial

theorem mk_modularFrobenius {R : Type*} [CommRing R]
    (E p : Polynomial R) (monic : E.Monic) (t : Nat) :
    AdjoinRoot.mk E (modularFrobenius E t p) = AdjoinRoot.mk E p ^ (2 ^ t) := by
  rw [modularFrobenius_eq_pow_modByMonic]
  calc
    _ = AdjoinRoot.mk E (p ^ (2 ^ t)) :=
      AdjoinRoot.mk_leftInverse monic (AdjoinRoot.mk E (p ^ (2 ^ t)))
    _ = _ := map_pow _ _ _

theorem sourcePolynomial_unpacked_frobenius (s v : Nat) (bits count : List Bool) :
    sourcePolynomial s (3 ^ v)
      (transposeBits (2 * 3 ^ s) (3 ^ v)
        (frobeniusBits (transposeBits (3 ^ v) (2 * 3 ^ s) bits)
          (trinomialBits (3 ^ (s + v))) count)) =
      modularFrobenius (extensionModulus s v) count.length
        (sourcePolynomial s (3 ^ v) bits) := by
  let : Fact (Irreducible (binaryModulus s)) := ⟨binaryModulus_irreducible s⟩
  let packed := transposeBits (3 ^ v) (2 * 3 ^ s) bits
  let powered := frobeniusBits packed (trinomialBits (3 ^ (s + v))) count
  let unpacked := transposeBits (2 * 3 ^ s) (3 ^ v) powered
  have width : powered.length = (2 * 3 ^ s) * 3 ^ v := by
    rw [show powered = frobeniusBits packed (trinomialBits (3 ^ (s + v))) count from rfl,
      frobeniusBits_binaryModulus_length, pow_add]
    ring
  have repack : transposeBits (3 ^ v) (2 * 3 ^ s) unpacked = powered :=
    transposeBits_transposeBits_of_length _ _ _ width
  have quotient : AdjoinRoot.mk (extensionModulus s v) (sourcePolynomial s (3 ^ v) unpacked) =
      AdjoinRoot.mk (extensionModulus s v) (sourcePolynomial s (3 ^ v) bits) ^
        (2 ^ count.length) := by
    calc
      _ = binaryExtensionEquiv s v
          (BinaryFieldCodec.decode (s + v)
            (transposeBits (3 ^ v) (2 * 3 ^ s) unpacked)) :=
        (binaryExtensionEquiv_decode_transpose s v unpacked).symm
      _ = binaryExtensionEquiv s v (BinaryFieldCodec.decode (s + v) powered) := by rw [repack]
      _ = _ := by
        rw [show powered = frobeniusBits packed (trinomialBits (3 ^ (s + v))) count from rfl,
          BinaryFieldCodec.decode_frobeniusBits _ _ _ _ (ofBits_trinomialBits_pow_three _),
          map_pow, binaryExtensionEquiv_decode_transpose]
  have classes := quotient.trans
    (mk_modularFrobenius (extensionModulus s v) (sourcePolynomial s (3 ^ v) bits)
      (extensionModulus_monic s v) count.length).symm
  have leftDegree : (sourcePolynomial s (3 ^ v) unpacked).degree <
      (extensionModulus s v).degree := by
    rw [Polynomial.degree_eq_natDegree (extensionModulus_monic s v).ne_zero,
      extensionModulus_natDegree]
    exact sourcePolynomial_degree_lt _ _ _
  have rightDegree := modularFrobenius_degree_lt (extensionModulus s v)
    (sourcePolynomial s (3 ^ v) bits) (extensionModulus_monic s v) count.length
  have same := congrArg (AdjoinRoot.modByMonicHom (extensionModulus_monic s v)) classes
  simpa only [AdjoinRoot.modByMonicHom_mk,
    (Polynomial.modByMonic_eq_self_iff (extensionModulus_monic s v)).mpr leftDegree,
    (Polynomial.modByMonic_eq_self_iff (extensionModulus_monic s v)).mpr rightDegree] using same

theorem decode_condenserCoordinateBits (s v : Nat)
    (coeffs halfDegree extensionCount seed powerCount : List Bool)
    (half : halfDegree.length = 3 ^ s) (extension : extensionCount.length = 3 ^ v) :
    BinaryFieldCodec.decode s
      (condenserCoordinateBits coeffs halfDegree extensionCount seed powerCount) =
        (modularFrobenius (extensionModulus s v) powerCount.length
          (sourcePolynomial s (3 ^ v) coeffs)).eval (BinaryFieldCodec.decode s seed) := by
  simp only [condenserCoordinateBits, half, extension, ← pow_add]
  rw [decode_blockEvalBits, extension, sourcePolynomial_unpacked_frobenius]

end Algebraic.Cutwidth.Extractor.Internal
