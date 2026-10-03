/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Encoding.BitPolynomial.BlockEval.Defs
public import Complexitylib.Encoding.BitPolynomial.Frobenius.Defs
public import Complexitylib.Encoding.BitPolynomial.Transpose.Defs
public import Complexitylib.Encoding.BitPolynomial.Trinomial.Defs

/-!
# Runtime binary program for polynomial condensation

Source coefficients are consecutive blocks of width twice the half-degree
word's length. Transposition packs them for modular Frobenius iteration;
the inverse transposition restores the blocks for evaluation at the seed.
Every dimension and iteration count is supplied at runtime as a word length.

The output concatenates fixed-width coordinates without list framing. These
are total list programs, including zero dimensions and malformed paired
inputs. Their interpretation in finite fields is a separate correctness
theorem requiring the intended powers-of-three dimensions.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Extractor

open Complexity Complexity.BitPolynomial

/-- One condenser coordinate, with a runtime number of modular squarings. -/
def condenserCoordinateBits (coeffs halfDegree extensionCount seed powerCount : List Bool) :
    List Bool :=
  let b := 2 * halfDegree.length
  let d := extensionCount.length
  let packed := transposeBits d b coeffs
  let powered := frobeniusBits packed (trinomialBits (halfDegree.length * d)) powerCount
  let unpacked := transposeBits b d powered
  blockEvalBits unpacked b seed (trinomialBits halfDegree.length) extensionCount

/-- Consecutive coordinates use `stride.length * i` modular squarings. -/
def condenserBits (coeffs halfDegree extensionCount seed stride count : List Bool) : List Bool :=
  (List.range count.length).flatMap fun i =>
    condenserCoordinateBits coeffs halfDegree extensionCount seed
      (List.replicate (stride.length * i) true)

/-- Runtime codec: `pair (pair (pair coeffs halfDegree) (pair extensionCount seed))
(pair stride count)`. The result contains coordinate bits, without the seed. -/
def condenserEval (z : List Bool) : List Bool :=
  let source := pairFst (pairFst z)
  let field := pairSnd (pairFst z)
  let counts := pairSnd z
  condenserBits (pairFst source) (pairSnd source) (pairFst field) (pairSnd field)
    (pairFst counts) (pairSnd counts)

end Algebraic.Cutwidth.Extractor
