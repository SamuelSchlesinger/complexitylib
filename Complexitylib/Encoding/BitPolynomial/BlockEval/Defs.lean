/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Encoding.BitPolynomial.Addition.Defs
public import Complexitylib.Encoding.BitPolynomial.Remainder.Defs

/-!
# Horner evaluation of flat binary coefficient blocks

Block `j` consists of at most `width` bits beginning at `j*width`, with absent
bits interpreted as zero by the polynomial codec. Blocks occur in increasing
polynomial degree. The count-list fold processes them from highest to lowest
using the index `total - tail.length - 1`.

Every state has the modulus degree in bits. A zero modulus explicitly gives
an empty state, and a zero count starts from the zero polynomial. The encoded
evaluator reads `pair (pair (pair coeffs widthWord) (pair seed modulus)) count`;
width and count are the lengths of their runtime words.
-/

@[expose] public section

namespace Complexity
namespace BitPolynomial

/-- A coefficient block, with missing high coefficients implicitly equal to zero. -/
def coefficientBlock (coeffs : List Bool) (width j : Nat) : List Bool :=
  (coeffs.drop (j * width)).take width

/-- One Horner step, guarded to return the empty list for a zero modulus. -/
def blockEvalStep (coefficient seed modulus state : List Bool) : List Bool :=
  if significantLength modulus = 0 then [] else
    remainderBits (addBits coefficient (mulBits seed state)) modulus

/-- A tail-first fold visiting coefficient indices `total-1`, `total-2`, and so on.
The partial-fold semantic invariant requires the count length to be at most `total`. -/
def blockEvalScan (coeffs : List Bool) (width : Nat) (seed modulus : List Bool)
    (total : Nat) : List Bool → List Bool
  | [] => List.replicate (significantLength modulus - 1) false
  | _ :: tail => blockEvalStep (coefficientBlock coeffs width (total - tail.length - 1))
      seed modulus (blockEvalScan coeffs width seed modulus total tail)

/-- Evaluate exactly as many coefficient blocks as there are bits in `count`. -/
def blockEvalBits (coeffs : List Bool) (width : Nat) (seed modulus count : List Bool) :
    List Bool :=
  blockEvalScan coeffs width seed modulus count.length count

/-- The total paired-input evaluator for a flat sequence of binary coefficient blocks. -/
def blockEval (z : List Bool) : List Bool :=
  let payload := pairFst z
  let coefficients := pairFst payload
  let point := pairSnd payload
  blockEvalBits (pairFst coefficients) (pairSnd coefficients).length
    (pairFst point) (pairSnd point) (pairSnd z)

end BitPolynomial
end Complexity
