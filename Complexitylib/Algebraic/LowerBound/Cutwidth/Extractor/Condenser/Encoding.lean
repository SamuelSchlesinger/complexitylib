/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Encoding.Defs
public import Complexitylib.Classes.P.Defs
public import Complexitylib.Tactic.PolyTime.Init
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Encoding.Internal

/-!
# A uniform runtime program for polynomial condensation

One polynomial-time evaluator handles all coefficient lists, seeds, unary
dimensions, and iteration counts. Its output concatenates fixed-width
coordinates, which can be recovered by taking consecutive blocks.

The results here describe the total program and its resource bound. They
impose no field or irreducibility assumptions; the finite-field meaning of
the generated trinomials and packed arithmetic is proved separately.
-/

public section

namespace Algebraic.Cutwidth.Extractor

open Complexity Complexity.BitPolynomial

/-- Each coordinate has the requested coefficient width, including width zero. -/
theorem condenserCoordinateBits_length
    (coeffs halfDegree extensionCount seed powerCount : List Bool) :
    (condenserCoordinateBits coeffs halfDegree extensionCount seed powerCount).length =
      2 * halfDegree.length :=
  Internal.condenserCoordinateBits_length coeffs halfDegree extensionCount seed powerCount

/-- The output contains exactly the requested number of fixed-width coordinates. -/
theorem condenserBits_length
    (coeffs halfDegree extensionCount seed stride count : List Bool) :
    (condenserBits coeffs halfDegree extensionCount seed stride count).length =
      count.length * (2 * halfDegree.length) :=
  Internal.condenserBits_length coeffs halfDegree extensionCount seed stride count

/-- Taking the `i`th output block recovers the coordinate with `stride.length * i`
modular squarings. -/
theorem coefficientBlock_condenserBits
    (coeffs halfDegree extensionCount seed stride count : List Bool)
    (i : Nat) (hi : i < count.length) :
    coefficientBlock (condenserBits coeffs halfDegree extensionCount seed stride count)
        (2 * halfDegree.length) i =
      condenserCoordinateBits coeffs halfDegree extensionCount seed
        (List.replicate (stride.length * i) true) :=
  Internal.coefficientBlock_condenserBits coeffs halfDegree extensionCount seed stride count i hi

/-- The paired evaluator implements the six-argument list program. -/
theorem condenserEval_pair
    (coeffs halfDegree extensionCount seed stride count : List Bool) :
    condenserEval
        (pair (pair (pair coeffs halfDegree) (pair extensionCount seed)) (pair stride count)) =
      condenserBits coeffs halfDegree extensionCount seed stride count :=
  Internal.condenserEval_pair coeffs halfDegree extensionCount seed stride count

/-- Even malformed paired inputs have a quadratic output-length bound. -/
theorem condenserEval_length_le (z : List Bool) :
    (condenserEval z).length ≤ 2 * z.length ^ 2 :=
  Internal.condenserEval_length_le z

/-- One coordinate is uniformly polynomial-time for polynomial-time runtime operands. -/
@[polytime] theorem condenserCoordinateBits_mem_FP
    {coeffs halfDegree extensionCount seed powerCount : List Bool → List Bool}
    (hcoeffs : coeffs ∈ FP) (hhalfDegree : halfDegree ∈ FP)
    (hextensionCount : extensionCount ∈ FP) (hseed : seed ∈ FP) (hpowerCount : powerCount ∈ FP) :
    (fun z => condenserCoordinateBits
      (coeffs z) (halfDegree z) (extensionCount z) (seed z) (powerCount z)) ∈ FP :=
  Internal.condenserCoordinateBits_mem_FP hcoeffs hhalfDegree hextensionCount hseed hpowerCount

/-- The coordinate concatenation is uniformly polynomial-time in all runtime operands. -/
@[polytime] theorem condenserBits_mem_FP
    {coeffs halfDegree extensionCount seed stride count : List Bool → List Bool}
    (hcoeffs : coeffs ∈ FP) (hhalfDegree : halfDegree ∈ FP)
    (hextensionCount : extensionCount ∈ FP) (hseed : seed ∈ FP)
    (hstride : stride ∈ FP) (hcount : count ∈ FP) :
    (fun z => condenserBits
      (coeffs z) (halfDegree z) (extensionCount z) (seed z) (stride z) (count z)) ∈ FP :=
  Internal.condenserBits_mem_FP hcoeffs hhalfDegree hextensionCount hseed hstride hcount

/-- A single polynomial-time machine computes the paired runtime condenser program. -/
@[polytime] theorem condenserEval_mem_FP : condenserEval ∈ FP :=
  Internal.condenserEval_mem_FP

end Algebraic.Cutwidth.Extractor
