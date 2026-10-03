/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Modulus.Binary.Encoding.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Modulus.Binary
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Polynomial.Defs
public import Complexitylib.Classes.P.Defs
public import Complexitylib.Tactic.PolyTime.Init
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Modulus.Binary.Encoding.Internal

/-!
# Uniform encoded construction of the binary modulus family

The runtime trinomial generator constructs the monic irreducible family
`X^(2 * 3^s) + X^(3^s) + 1`. Rounding a requested unary half-degree costs
at most a factor of three, with a constant allowance at the empty input.
The single evaluator generates that modulus and performs modular squaring
in polynomial time in the dividend, target, and unary squaring-count lengths.

This connects the concrete bit-list arithmetic to `modularFrobenius`.
`Condenser.Encoding.Correctness` uses the extension-field packing to assemble
the complete seeded condenser evaluator. No search through a field or
irreducible polynomials is used.
-/

public section

namespace Algebraic.Cutwidth.Extractor

open Complexity Complexity.BitPolynomial

/-- The sparse coefficient generator is the explicit irreducible binary family. -/
theorem ofBits_trinomialBits_pow_three (s : Nat) :
    ofBits (trinomialBits (3 ^ s)) = binaryModulus s :=
  Internal.ofBits_trinomialBits_pow_three s

/-- Rounding the requested half-degree chooses the corresponding family member. -/
theorem ofBits_roundedTrinomialEval (target : List Bool) :
    ofBits (roundedTrinomialEval target) = binaryModulus (Nat.clog 3 target.length) :=
  Internal.ofBits_roundedTrinomialEval target

/-- The generated degree covers the target with a linear bound, even at zero. -/
theorem roundedTrinomialEval_degree_bounds (target : List Bool) :
    2 * target.length ≤ (ofBits (roundedTrinomialEval target)).natDegree ∧
      (ofBits (roundedTrinomialEval target)).natDegree ≤ 6 * target.length + 2 :=
  Internal.roundedTrinomialEval_degree_bounds target

/-- Encoded modular squaring agrees with the condenser's polynomial operation. -/
theorem ofBits_frobeniusBits_binaryModulus (s : Nat) (a count : List Bool) :
    ofBits (frobeniusBits a (trinomialBits (3 ^ s)) count) =
      modularFrobenius (binaryModulus s) count.length (ofBits a) :=
  Internal.ofBits_frobeniusBits_binaryModulus s a count

/-- Every encoded state occupies exactly one binary field element. -/
theorem frobeniusBits_binaryModulus_length (s : Nat) (a count : List Bool) :
    (frobeniusBits a (trinomialBits (3 ^ s)) count).length = 2 * 3 ^ s :=
  Internal.frobeniusBits_binaryModulus_length s a count

/-- The public evaluator reads the dividend, half-degree target, and count. -/
theorem encodedBinaryFrobenius_pair (a target count : List Bool) :
    encodedBinaryFrobenius (pair (pair a target) count) =
      frobeniusBits a (roundedTrinomialEval target) count :=
  Internal.encodedBinaryFrobenius_pair a target count

/-- Generating the modulus and then running the loop computes modular Frobenius. -/
theorem ofBits_encodedBinaryFrobenius (a target count : List Bool) :
    ofBits (encodedBinaryFrobenius (pair (pair a target) count)) =
      modularFrobenius (binaryModulus (Nat.clog 3 target.length)) count.length (ofBits a) :=
  Internal.ofBits_encodedBinaryFrobenius a target count

/-- The evaluator's output has the generated field's exact bit width. -/
theorem encodedBinaryFrobenius_length (a target count : List Bool) :
    (encodedBinaryFrobenius (pair (pair a target) count)).length =
      2 * 3 ^ Nat.clog 3 target.length :=
  Internal.encodedBinaryFrobenius_length a target count

/-- Modulus construction and modular squaring form one uniform polynomial-time program. -/
@[polytime] theorem encodedBinaryFrobenius_mem_FP : encodedBinaryFrobenius ∈ FP :=
  Internal.encodedBinaryFrobenius_mem_FP

end Algebraic.Cutwidth.Extractor
