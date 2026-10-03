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
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Encoding
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Encoding.Correctness.Internal.Frobenius
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Modulus.Binary.Codec

/-!
# The complete runtime program implements the polynomial condenser

Each fixed-width output block is the corresponding modular-Frobenius
coordinate evaluated at the seed. Concatenation preserves their order,
and the total paired-input evaluator agrees with this same list program.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

open Complexity Complexity.BitPolynomial

theorem condenserBits_correct (s v : Nat)
    (coeffs halfDegree extensionCount seed stride count : List Bool)
    (half : halfDegree.length = 3 ^ s) (extension : extensionCount.length = 3 ^ v) :
    (fun i : Fin count.length => BinaryFieldCodec.decode s
      (coefficientBlock (condenserBits coeffs halfDegree extensionCount seed stride count)
        (2 * 3 ^ s) i.val)) =
      polynomialCondenser (extensionModulus s v) stride.length count.length
        (sourcePolynomial s (3 ^ v) coeffs) (BinaryFieldCodec.decode s seed) := by
  funext i
  have block := coefficientBlock_condenserBits
    coeffs halfDegree extensionCount seed stride count i.val i.isLt
  rw [half] at block
  rw [block, decode_condenserCoordinateBits s v _ _ _ _ _ half extension,
    List.length_replicate]
  rfl

theorem condenserEval_correct (s v : Nat)
    (coeffs halfDegree extensionCount seed stride count : List Bool)
    (half : halfDegree.length = 3 ^ s) (extension : extensionCount.length = 3 ^ v) :
    (fun i : Fin count.length => BinaryFieldCodec.decode s
      (coefficientBlock
        (condenserEval
          (pair (pair (pair coeffs halfDegree) (pair extensionCount seed)) (pair stride count)))
        (2 * 3 ^ s) i.val)) =
      polynomialCondenser (extensionModulus s v) stride.length count.length
        (sourcePolynomial s (3 ^ v) coeffs) (BinaryFieldCodec.decode s seed) := by
  rw [condenserEval_pair]
  exact condenserBits_correct s v coeffs halfDegree extensionCount seed stride count half extension

theorem decodedCondenser_eq (s v : Nat)
    (halfDegree extensionCount stride count bits : List Bool)
    (seed : AdjoinRoot (binaryModulus s))
    (half : halfDegree.length = 3 ^ s) (extension : extensionCount.length = 3 ^ v) :
    decodedCondenser s halfDegree extensionCount stride count bits seed =
      polynomialCondenser (extensionModulus s v) stride.length count.length
        (sourcePolynomial s (3 ^ v) bits) seed := by
  unfold decodedCondenser
  simpa only [BinaryFieldCodec.decode_encode] using
    condenserBits_correct s v bits halfDegree extensionCount (BinaryFieldCodec.encode s seed)
      stride count half extension

end Algebraic.Cutwidth.Extractor.Internal
