/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Encoding.BitPolynomial.BlockEval.Defs
public import Mathlib.Algebra.Polynomial.Div
import Complexitylib.Encoding.BitPolynomial.BlockEval.Internal

/-!
# Correct evaluation of runtime coefficient blocks

For every nonzero binary modulus, the evaluator computes
`sum_{j<count} ofBits(block j) * ofBits(seed)^j` modulo that modulus.
The coefficient blocks are consecutive low-to-high slices of one flat bit
string. Short or absent blocks contribute implicit high zeros. Width zero,
count zero, padded inputs, and constant-one moduli are covered.

The Horner fold runs from high coefficient indices to low indices, retaining
exactly the modulus degree in bits. Its partial-fold theorem explicitly
requires the remaining count length to be at most the total count. A zero
modulus returns the empty list. The machine certificate is in
`Complexitylib.Classes.P.BitPolynomial.BlockEval`.
-/

public section

namespace Complexity
namespace BitPolynomial

open scoped BigOperators

/-- A coefficient slice never exceeds its requested width. -/
theorem coefficientBlock_length_le (coeffs : List Bool) (width j : Nat) :
    (coefficientBlock coeffs width j).length ≤ width :=
  Internal.coefficientBlock_length_le coeffs width j

/-- Each guarded Horner step restores the modulus-degree width. -/
theorem blockEvalStep_length (coefficient seed modulus state : List Bool) :
    (blockEvalStep coefficient seed modulus state).length = significantLength modulus - 1 :=
  Internal.blockEvalStep_length coefficient seed modulus state

/-- Every partial fold has the same width, including the initial zero state. -/
theorem blockEvalScan_length (coeffs : List Bool) (width : Nat) (seed modulus : List Bool)
    (total : Nat) (count : List Bool) :
    (blockEvalScan coeffs width seed modulus total count).length = significantLength modulus - 1 :=
  Internal.blockEvalScan_length coeffs width seed modulus total count

/-- The full evaluator has exact modulus-degree output width. -/
theorem blockEvalBits_length (coeffs : List Bool) (width : Nat) (seed modulus count : List Bool) :
    (blockEvalBits coeffs width seed modulus count).length = significantLength modulus - 1 :=
  Internal.blockEvalBits_length coeffs width seed modulus count

/-- The output is at most the supplied modulus length, for all inputs. -/
theorem blockEvalBits_length_le (coeffs : List Bool) (width : Nat)
    (seed modulus count : List Bool) :
    (blockEvalBits coeffs width seed modulus count).length ≤ modulus.length :=
  Internal.blockEvalBits_length_le coeffs width seed modulus count

/-- A zero modulus gives empty output for every coefficient string, seed, and count. -/
theorem blockEvalBits_of_modulus_zero (coeffs : List Bool) (width : Nat)
    (seed modulus count : List Bool) (zero : ofBits modulus = 0) :
    blockEvalBits coeffs width seed modulus count = [] :=
  Internal.blockEvalBits_of_modulus_zero coeffs width seed modulus count zero

/-- A Horner step adds the next coefficient to the seed times the prior state. -/
theorem ofBits_blockEvalStep (coefficient seed modulus state : List Bool)
    (nonzero : ofBits modulus ≠ 0) :
    ofBits (blockEvalStep coefficient seed modulus state) =
      (ofBits coefficient + ofBits seed * ofBits state) %ₘ ofBits modulus :=
  Internal.ofBits_blockEvalStep coefficient seed modulus state nonzero

/-- A partial fold evaluates the highest requested blocks, starting at exponent zero. -/
theorem ofBits_blockEvalScan (coeffs : List Bool) (width : Nat) (seed modulus : List Bool)
    (total : Nat) (count : List Bool) (nonzero : ofBits modulus ≠ 0)
    (bound : count.length ≤ total) :
    ofBits (blockEvalScan coeffs width seed modulus total count) =
      (∑ j ∈ Finset.range count.length,
        ofBits (coefficientBlock coeffs width (total - count.length + j)) *
          ofBits seed ^ j) %ₘ ofBits modulus :=
  Internal.ofBits_blockEvalScan coeffs width seed modulus total count nonzero bound

/-- The full fold equals the coefficient-block power sum modulo the runtime modulus. -/
theorem ofBits_blockEvalBits (coeffs : List Bool) (width : Nat)
    (seed modulus count : List Bool) (nonzero : ofBits modulus ≠ 0) :
    ofBits (blockEvalBits coeffs width seed modulus count) =
      (∑ j ∈ Finset.range count.length,
        ofBits (coefficientBlock coeffs width j) * ofBits seed ^ j) %ₘ ofBits modulus :=
  Internal.ofBits_blockEvalBits coeffs width seed modulus count nonzero

/-- The codec supplies all five runtime inputs, with width given by its word length. -/
theorem blockEval_pair (coeffs widthWord seed modulus count : List Bool) :
    blockEval (pair (pair (pair coeffs widthWord) (pair seed modulus)) count) =
      blockEvalBits coeffs widthWord.length seed modulus count :=
  Internal.blockEval_pair coeffs widthWord seed modulus count

/-- The total encoded evaluator's output is bounded by its input length. -/
theorem blockEval_length_le (z : List Bool) : (blockEval z).length ≤ z.length :=
  Internal.blockEval_length_le z

end BitPolynomial
end Complexity
