/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Encoding.Correctness.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Modulus.Binary.Extension
public import Complexitylib.Encoding.BitPolynomial.Transpose.Defs
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Encoding.Correctness.Internal.Basic
import Complexitylib.Encoding.BitPolynomial.BlockEval
import Complexitylib.Encoding.BitPolynomial.Transpose

/-!
# Bit transposition realizes the extension-field coefficient packing

A coefficient bit at row `j`, column `i` contributes `t^i * u^j` in the
binomial extension. Since `t = u^d`, the same bit occupies position `d*i+j`
in the larger binary quotient. Finite-sum reindexing proves that the runtime
matrix transpose implements this exact algebraic identification.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

open Complexity.BitPolynomial
open scoped Classical

theorem eval₂_ofBits_transpose {R : Type*} [CommSemiring R] (f : ZMod 2 →+* R)
    (u : R) (rows cols : Nat) (bits : List Bool) :
    (ofBits (transposeBits rows cols bits)).eval₂ f u =
      ∑ j : Fin rows, (ofBits (coefficientBlock bits cols j.val)).eval₂ f (u ^ rows) *
        u ^ j.val := by
  have length : (transposeBits rows cols bits).length ≤ cols * rows := by
    rw [transposeBits_length, Nat.mul_comm]
  rw [eval₂_ofBits_padded f u _ (cols * rows) length,
    sum_fin_mul cols rows (fun k =>
      f ((transposeBits rows cols bits)[k]?.getD false).toNat * u ^ k), Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro row _
  rw [eval₂_ofBits_padded f (u ^ rows) _ cols
    (Complexity.BitPolynomial.coefficientBlock_length_le _ _ _), Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro col _
  rw [transposeBits_getD_coord rows cols bits row.val col.val row.isLt col.isLt,
    coefficientBlock_getD bits cols row.val col.val col.isLt]
  simp only [← pow_mul, Nat.mul_comm rows col.val, pow_add, mul_assoc]

theorem binaryExtensionEquiv_decode_transpose (s v : Nat) (bits : List Bool) :
    binaryExtensionEquiv s v
      (BinaryFieldCodec.decode (s + v) (transposeBits (3 ^ v) (2 * 3 ^ s) bits)) =
        AdjoinRoot.mk (extensionModulus s v) (sourcePolynomial s (3 ^ v) bits) := by
  apply (binaryExtensionEquiv s v).symm.injective
  rw [AlgEquiv.symm_apply_apply, binaryExtensionEquiv_symm_mk,
    sourcePolynomial, eval₂_ofFn]
  rw [BinaryFieldCodec.decode, ← AdjoinRoot.aeval_eq, Polynomial.aeval_def,
    eval₂_ofBits_transpose]
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  change _ = (binaryExtensionEquiv s v).symm
    (AdjoinRoot.of (extensionModulus s v)
      (AdjoinRoot.mk (binaryModulus s)
        (ofBits (coefficientBlock bits (2 * 3 ^ s) j.val))))
  rw [binaryExtensionEquiv_symm_of_mk, Polynomial.aeval_def]

end Algebraic.Cutwidth.Extractor.Internal
