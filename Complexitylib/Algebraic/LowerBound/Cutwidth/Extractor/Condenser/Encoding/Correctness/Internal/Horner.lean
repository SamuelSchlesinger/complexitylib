/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Encoding.Correctness.Defs
public import Complexitylib.Encoding.BitPolynomial.Trinomial.Defs
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Encoding.Correctness.Internal.Basic
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Modulus.Binary.Encoding
import Complexitylib.Encoding.BitPolynomial.BlockEval

/-!
# Decoding Horner evaluation as source-polynomial evaluation

The public bit evaluator computes its coefficient power sum modulo the binary
modulus. Taking the quotient removes that remainder, and quotient addition and
multiplication give evaluation of the decoded source polynomial. The equality
holds for arbitrary input lengths, including short and missing blocks.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

open Complexity.BitPolynomial

theorem decode_blockEvalBits (s : Nat) (coeffs seed count : List Bool) :
    BinaryFieldCodec.decode s
      (blockEvalBits coeffs (2 * 3 ^ s) seed (trinomialBits (3 ^ s)) count) =
        (sourcePolynomial s count.length coeffs).eval (BinaryFieldCodec.decode s seed) := by
  have nonzero : ofBits (trinomialBits (3 ^ s)) ≠ 0 := by
    rw [ofBits_trinomialBits_pow_three]
    exact (binaryModulus_monic s).ne_zero
  have remainder (p : Polynomial (ZMod 2)) :
      AdjoinRoot.mk (binaryModulus s) (p %ₘ binaryModulus s) =
        AdjoinRoot.mk (binaryModulus s) p :=
    AdjoinRoot.mk_leftInverse (binaryModulus_monic s) (AdjoinRoot.mk (binaryModulus s) p)
  rw [BinaryFieldCodec.decode, ofBits_blockEvalBits _ _ _ _ _ nonzero,
    ofBits_trinomialBits_pow_three, remainder, sourcePolynomial,
    ← Polynomial.eval₂_id, eval₂_ofFn]
  simp only [map_sum, map_mul, map_pow, RingHom.id_apply, BinaryFieldCodec.decode,
    Finset.sum_range]

end Algebraic.Cutwidth.Extractor.Internal
