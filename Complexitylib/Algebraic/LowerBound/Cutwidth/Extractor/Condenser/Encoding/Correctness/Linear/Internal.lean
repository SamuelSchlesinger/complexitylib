/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Encoding.Correctness.Defs
public import Complexitylib.Encoding.BitPolynomial.Addition.Defs
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Encoding.Correctness.Internal
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Encoding.Correctness.Internal.Basic
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Polynomial
import Complexitylib.Encoding.BitPolynomial
import Complexitylib.Encoding.BitPolynomial.Addition
import Complexitylib.Encoding.BitPolynomial.BlockEval
import Mathlib.Algebra.CharP.Algebra

/-!
# Source additivity of the decoded runtime condenser

Every coefficient block preserves binary polynomial addition even when the
source lists have different lengths. The source-polynomial map is therefore
additive under padded XOR. The checked runtime-program identity transfers
the characteristic-two polynomial condenser's additivity to the actual
decoded output. All-false inputs of every length give zero outputs.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

open Complexity.BitPolynomial

private theorem ofBits_coefficientBlock_addBits (a b : List Bool) (width j : Nat) :
    ofBits (coefficientBlock (addBits a b) width j) =
      ofBits (coefficientBlock a width j) + ofBits (coefficientBlock b width j) := by
  ext i
  rw [Polynomial.coeff_add, ofBits_coeff, ofBits_coeff, ofBits_coeff]
  by_cases bound : i < width
  · rw [coefficientBlock_getD _ _ _ _ bound, coefficientBlock_getD _ _ _ _ bound,
      coefficientBlock_getD _ _ _ _ bound]
    have entry := congrArg (fun p : Polynomial (ZMod 2) => p.coeff (j * width + i))
      (ofBits_addBits a b)
    simpa only [Polynomial.coeff_add, ofBits_coeff] using entry
  · have outside (bits : List Bool) : (coefficientBlock bits width j).length ≤ i :=
      (coefficientBlock_length_le bits width j).trans (Nat.le_of_not_gt bound)
    simp only [List.getElem?_eq_none (outside _), Option.getD_none, Bool.toNat_false,
      Nat.cast_zero, zero_add]

private theorem ofBits_replicate_false (n : Nat) : ofBits (List.replicate n false) = 0 := by
  ext i
  rw [ofBits_coeff]
  simp only [List.getElem?_replicate]
  split_ifs <;> rfl

theorem sourcePolynomial_addBits (s d : Nat) (a b : List Bool) :
    sourcePolynomial s d (addBits a b) = sourcePolynomial s d a + sourcePolynomial s d b := by
  classical
  unfold sourcePolynomial
  rw [← map_add]
  apply congrArg (Polynomial.ofFn d)
  funext j
  change BinaryFieldCodec.decode s (coefficientBlock (addBits a b) (2 * 3 ^ s) j.val) =
    BinaryFieldCodec.decode s (coefficientBlock a (2 * 3 ^ s) j.val) +
      BinaryFieldCodec.decode s (coefficientBlock b (2 * 3 ^ s) j.val)
  simp only [BinaryFieldCodec.decode, ofBits_coefficientBlock_addBits, map_add]

theorem sourcePolynomial_replicate_false (s d n : Nat) :
    sourcePolynomial s d (List.replicate n false) = 0 := by
  simp only [sourcePolynomial, coefficientBlock, List.drop_replicate, List.take_replicate,
    BinaryFieldCodec.decode, ofBits_replicate_false, map_zero]
  exact Polynomial.ofFn_zero d

theorem sourcePolynomial_nil (s d : Nat) : sourcePolynomial s d [] = 0 :=
  sourcePolynomial_replicate_false s d 0

theorem decodedCondenser_addBits (s v : Nat)
    (halfDegree extensionCount stride count a b : List Bool)
    (seed : AdjoinRoot (binaryModulus s))
    (half : halfDegree.length = 3 ^ s) (extension : extensionCount.length = 3 ^ v) :
    decodedCondenser s halfDegree extensionCount stride count (addBits a b) seed =
      decodedCondenser s halfDegree extensionCount stride count a seed +
        decodedCondenser s halfDegree extensionCount stride count b seed := by
  let : Fact (Irreducible (binaryModulus s)) := ⟨binaryModulus_irreducible s⟩
  let : CharP (AdjoinRoot (binaryModulus s)) 2 :=
    charP_of_injective_ringHom (AdjoinRoot.of (binaryModulus s)).injective 2
  have correct (bits : List Bool) :=
    decodedCondenser_eq s v halfDegree extensionCount stride count bits seed half extension
  simp only [correct, sourcePolynomial_addBits, polynomialCondenser_add]

theorem decodedCondenser_replicate_false (s v n : Nat)
    (halfDegree extensionCount stride count : List Bool)
    (seed : AdjoinRoot (binaryModulus s))
    (half : halfDegree.length = 3 ^ s) (extension : extensionCount.length = 3 ^ v) :
    decodedCondenser s halfDegree extensionCount stride count
      (List.replicate n false) seed = 0 := by
  rw [decodedCondenser_eq s v _ _ _ _ _ _ half extension,
    sourcePolynomial_replicate_false, polynomialCondenser_zero]

theorem decodedCondenser_nil (s v : Nat)
    (halfDegree extensionCount stride count : List Bool)
    (seed : AdjoinRoot (binaryModulus s))
    (half : halfDegree.length = 3 ^ s) (extension : extensionCount.length = 3 ^ v) :
    decodedCondenser s halfDegree extensionCount stride count [] seed = 0 :=
  decodedCondenser_replicate_false s v 0 halfDegree extensionCount stride count seed half extension

end Algebraic.Cutwidth.Extractor.Internal
