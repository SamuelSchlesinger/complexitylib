/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Encoding
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Encoding.Correctness.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Modulus.Binary.Extension
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Polynomial.Defs
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Encoding.Correctness.Internal
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Encoding.Correctness.Internal.Basic
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Encoding.Correctness.Internal.Packing
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Encoding.Correctness.Internal.Horner
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Encoding.Correctness.Internal.Frobenius
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Encoding.Correctness.Internal.Source

/-!
# A uniform encoded implementation of the polynomial condenser

For base-field width `b = 2 * 3^s` and extension degree `d = 3^v`, the runtime
program computes exactly the GUV polynomial map with modulus `X^d - t`,
where `t` is the named noncube root of the explicit binary field. Source
bits are consecutive coefficient blocks, the seed is one binary field
element, and the output is the coordinate vector in the same fixed-width
representation. Missing source bits are zero and excess bits are ignored.

The equivalence with the larger binary quotient justifies the transpositions
around modular squaring. Uniqueness of reduced representatives identifies
the intermediate extension polynomial before Horner evaluation. Thus the
uniform `FP` program in `Encoding` computes the map whose expansion and flat
lossless guarantees were proved in the condenser modules. Asymptotic budgets
for its unary parameters and the higher extractor construction are separate.
-/

public section

namespace Algebraic.Cutwidth.Extractor

open Complexity Complexity.BitPolynomial

/-- Interpreting a fixed number of coefficient blocks always gives a bounded-degree source. -/
theorem sourcePolynomial_degree_lt (s d : Nat) (bits : List Bool) :
    (sourcePolynomial s d bits).degree < (d : WithBot Nat) :=
  Internal.sourcePolynomial_degree_lt s d bits

/-- Within capacity, two inputs of the same length encode distinct source polynomials. -/
theorem sourcePolynomial_inj_of_length (s v n : Nat)
    (capacity : n ≤ (2 * 3 ^ s) * 3 ^ v) (a b : List Bool)
    (ha : a.length = n) (hb : b.length = n)
    (same : sourcePolynomial s (3 ^ v) a = sourcePolynomial s (3 ^ v) b) : a = b :=
  Internal.sourcePolynomial_inj_of_length s v n capacity a b ha hb same

/-- Padding to the coefficient rectangle preserves every fixed-length input source. -/
theorem sourcePolynomial_injectiveOn_length (s v n : Nat)
    (capacity : n ≤ (2 * 3 ^ s) * 3 ^ v) :
    Set.InjOn (sourcePolynomial s (3 ^ v)) {bits | bits.length = n} :=
  Internal.sourcePolynomial_injectiveOn_length s v n capacity

/-- The bit-matrix transpose is exactly the tower's coefficient-packing map. -/
theorem binaryExtensionEquiv_decode_transpose (s v : Nat) (bits : List Bool) :
    binaryExtensionEquiv s v
      (BinaryFieldCodec.decode (s + v) (transposeBits (3 ^ v) (2 * 3 ^ s) bits)) =
        AdjoinRoot.mk (extensionModulus s v) (sourcePolynomial s (3 ^ v) bits) :=
  Internal.binaryExtensionEquiv_decode_transpose s v bits

/-- Horner evaluation of arbitrary blocks decodes to source-polynomial evaluation. -/
theorem decode_blockEvalBits (s : Nat) (coeffs seed count : List Bool) :
    BinaryFieldCodec.decode s
      (blockEvalBits coeffs (2 * 3 ^ s) seed (trinomialBits (3 ^ s)) count) =
        (sourcePolynomial s count.length coeffs).eval (BinaryFieldCodec.decode s seed) :=
  Internal.decode_blockEvalBits s coeffs seed count

/-- Unpacking the modular binary power recovers the actual reduced extension polynomial. -/
theorem sourcePolynomial_unpacked_frobenius (s v : Nat) (bits count : List Bool) :
    sourcePolynomial s (3 ^ v)
      (transposeBits (2 * 3 ^ s) (3 ^ v)
        (frobeniusBits (transposeBits (3 ^ v) (2 * 3 ^ s) bits)
          (trinomialBits (3 ^ (s + v))) count)) =
      modularFrobenius (extensionModulus s v) count.length
        (sourcePolynomial s (3 ^ v) bits) :=
  Internal.sourcePolynomial_unpacked_frobenius s v bits count

/-- The computed coordinate is the modular-Frobenius polynomial evaluated at the seed. -/
theorem decode_condenserCoordinateBits (s v : Nat)
    (coeffs halfDegree extensionCount seed powerCount : List Bool)
    (half : halfDegree.length = 3 ^ s) (extension : extensionCount.length = 3 ^ v) :
    BinaryFieldCodec.decode s
      (condenserCoordinateBits coeffs halfDegree extensionCount seed powerCount) =
        (modularFrobenius (extensionModulus s v) powerCount.length
          (sourcePolynomial s (3 ^ v) coeffs)).eval (BinaryFieldCodec.decode s seed) :=
  Internal.decode_condenserCoordinateBits s v coeffs halfDegree extensionCount seed powerCount
    half extension

/-- All decoded output blocks equal the polynomial condenser, in the same coordinate order. -/
theorem condenserBits_correct (s v : Nat)
    (coeffs halfDegree extensionCount seed stride count : List Bool)
    (half : halfDegree.length = 3 ^ s) (extension : extensionCount.length = 3 ^ v) :
    (fun i : Fin count.length => BinaryFieldCodec.decode s
      (coefficientBlock (condenserBits coeffs halfDegree extensionCount seed stride count)
        (2 * 3 ^ s) i.val)) =
      polynomialCondenser (extensionModulus s v) stride.length count.length
        (sourcePolynomial s (3 ^ v) coeffs) (BinaryFieldCodec.decode s seed) :=
  Internal.condenserBits_correct s v coeffs halfDegree extensionCount seed stride count half extension

/-- The actual paired-input `FP` evaluator computes the proved polynomial map. -/
theorem condenserEval_correct (s v : Nat)
    (coeffs halfDegree extensionCount seed stride count : List Bool)
    (half : halfDegree.length = 3 ^ s) (extension : extensionCount.length = 3 ^ v) :
    (fun i : Fin count.length => BinaryFieldCodec.decode s
      (coefficientBlock
        (condenserEval
          (pair (pair (pair coeffs halfDegree) (pair extensionCount seed)) (pair stride count)))
        (2 * 3 ^ s) i.val)) =
      polynomialCondenser (extensionModulus s v) stride.length count.length
        (sourcePolynomial s (3 ^ v) coeffs) (BinaryFieldCodec.decode s seed) :=
  Internal.condenserEval_correct s v coeffs halfDegree extensionCount seed stride count half extension

/-- Canonically encoding the seed and decoding the output gives the exact polynomial map. -/
theorem decodedCondenser_eq (s v : Nat)
    (halfDegree extensionCount stride count bits : List Bool)
    (seed : AdjoinRoot (binaryModulus s))
    (half : halfDegree.length = 3 ^ s) (extension : extensionCount.length = 3 ^ v) :
    decodedCondenser s halfDegree extensionCount stride count bits seed =
      polynomialCondenser (extensionModulus s v) stride.length count.length
        (sourcePolynomial s (3 ^ v) bits) seed :=
  Internal.decodedCondenser_eq s v halfDegree extensionCount stride count bits seed half extension

end Algebraic.Cutwidth.Extractor
