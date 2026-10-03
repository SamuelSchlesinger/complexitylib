/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Modulus.Binary.Encoding.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Modulus.Binary.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Polynomial.Defs
public import Complexitylib.Classes.P.Defs
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Modulus.Binary
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Polynomial
import Complexitylib.Classes.P.BitPolynomial.Frobenius
import Complexitylib.Classes.P.BitPolynomial.Trinomial
import Complexitylib.Classes.P.Unary.Internal.Log
import Complexitylib.Encoding.BitPolynomial.Remainder
import Complexitylib.Tactic.PolyTime

/-!
# Correctness and cost of the generated binary modulus

The concrete coefficient generator agrees with the irreducible trinomial
family. Existing modular-squaring semantics then identify every bounded
runtime state with the polynomial condenser's Frobenius operation.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

open Complexity Complexity.BitPolynomial

theorem ofBits_trinomialBits_pow_three (s : Nat) :
    ofBits (trinomialBits (3 ^ s)) = binaryModulus s :=
  ofBits_trinomialBits (3 ^ s)

theorem ofBits_roundedTrinomialEval (target : List Bool) :
    ofBits (roundedTrinomialEval target) = binaryModulus (Nat.clog 3 target.length) :=
  ofBits_trinomialBits_pow_three _

theorem roundedTrinomialEval_degree_bounds (target : List Bool) :
    2 * target.length ≤ (ofBits (roundedTrinomialEval target)).natDegree ∧
      (ofBits (roundedTrinomialEval target)).natDegree ≤ 6 * target.length + 2 := by
  rw [ofBits_roundedTrinomialEval, binaryModulus_natDegree]
  have lower := Nat.le_pow_clog (b := 3) (by decide) target.length
  have upper := pow_clog_le_mul_add_one 3 target.length
  constructor <;> lia

theorem ofBits_frobeniusBits_binaryModulus (s : Nat) (a count : List Bool) :
    ofBits (frobeniusBits a (trinomialBits (3 ^ s)) count) =
      modularFrobenius (binaryModulus s) count.length (ofBits a) := by
  rw [ofBits_frobeniusBits, ofBits_trinomialBits_pow_three,
    modularFrobenius_eq_pow_modByMonic]
  rw [ofBits_trinomialBits_pow_three]
  exact (binaryModulus_monic s).ne_zero

theorem frobeniusBits_binaryModulus_length (s : Nat) (a count : List Bool) :
    (frobeniusBits a (trinomialBits (3 ^ s)) count).length = 2 * 3 ^ s := by
  rw [frobeniusBits_length, ← ofBits_natDegree]
  · rw [ofBits_trinomialBits_pow_three, binaryModulus_natDegree]
  · rw [ofBits_trinomialBits_pow_three]
    exact (binaryModulus_monic s).ne_zero

theorem encodedBinaryFrobenius_pair (a target count : List Bool) :
    encodedBinaryFrobenius (pair (pair a target) count) =
      frobeniusBits a (roundedTrinomialEval target) count := by
  simp only [encodedBinaryFrobenius, pairFst_pair, pairSnd_pair, frobeniusEval_pair]

theorem ofBits_encodedBinaryFrobenius (a target count : List Bool) :
    ofBits (encodedBinaryFrobenius (pair (pair a target) count)) =
      modularFrobenius (binaryModulus (Nat.clog 3 target.length)) count.length (ofBits a) := by
  rw [encodedBinaryFrobenius_pair]
  exact ofBits_frobeniusBits_binaryModulus _ a count

theorem encodedBinaryFrobenius_length (a target count : List Bool) :
    (encodedBinaryFrobenius (pair (pair a target) count)).length =
      2 * 3 ^ Nat.clog 3 target.length := by
  rw [encodedBinaryFrobenius_pair]
  exact frobeniusBits_binaryModulus_length _ a count

theorem encodedBinaryFrobenius_mem_FP : encodedBinaryFrobenius ∈ FP := by
  polytime [encodedBinaryFrobenius]

end Algebraic.Cutwidth.Extractor.Internal
