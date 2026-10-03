/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Encoding.Correctness.Defs
public import Complexitylib.Encoding.BitPolynomial.Addition.Defs
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Encoding.Correctness.Linear.Internal

/-!
# Source addition and zero preservation for the actual encoded condenser

Padded coefficientwise XOR represents addition of source polynomials for
arbitrary lists. For every semantic field seed, the decoded runtime program
therefore preserves source addition and sends every all-false input to zero.
The program is the existing `condenserBits` implementation behind
`decodedCondenser`, connected to the polynomial map by the checked correctness
theorem; no alternative implementation is introduced.

Only the two runtime dimension words must match their chosen powers of three.
No source-length, capacity, positive-count, or positive-stride premise is needed.
The characteristic-two structure is derived locally from the explicit binary
field, and no global instances are introduced. Polynomial-map linearity and
its source credits are documented in `Condenser.Polynomial`.
-/

public section

namespace Algebraic.Cutwidth.Extractor

open Complexity.BitPolynomial

/-- Padded XOR preserves source-polynomial addition, including unequal input lengths. -/
theorem sourcePolynomial_addBits (s d : Nat) (a b : List Bool) :
    sourcePolynomial s d (addBits a b) = sourcePolynomial s d a + sourcePolynomial s d b :=
  Internal.sourcePolynomial_addBits s d a b

/-- Every all-false source represents the zero polynomial, at every padding length. -/
theorem sourcePolynomial_replicate_false (s d n : Nat) :
    sourcePolynomial s d (List.replicate n false) = 0 :=
  Internal.sourcePolynomial_replicate_false s d n

/-- An empty source represents the zero polynomial. -/
theorem sourcePolynomial_nil (s d : Nat) : sourcePolynomial s d [] = 0 :=
  Internal.sourcePolynomial_nil s d

/-- For each field seed, the actual decoded program preserves padded source XOR. -/
theorem decodedCondenser_addBits (s v : Nat)
    (halfDegree extensionCount stride count a b : List Bool)
    (seed : AdjoinRoot (binaryModulus s))
    (half : halfDegree.length = 3 ^ s) (extension : extensionCount.length = 3 ^ v) :
    decodedCondenser s halfDegree extensionCount stride count (addBits a b) seed =
      decodedCondenser s halfDegree extensionCount stride count a seed +
        decodedCondenser s halfDegree extensionCount stride count b seed :=
  Internal.decodedCondenser_addBits s v halfDegree extensionCount stride count a b seed
    half extension

/-- Every padded zero source gives the zero vector of decoded output coordinates. -/
theorem decodedCondenser_replicate_false (s v n : Nat)
    (halfDegree extensionCount stride count : List Bool)
    (seed : AdjoinRoot (binaryModulus s))
    (half : halfDegree.length = 3 ^ s) (extension : extensionCount.length = 3 ^ v) :
    decodedCondenser s halfDegree extensionCount stride count
      (List.replicate n false) seed = 0 :=
  Internal.decodedCondenser_replicate_false s v n halfDegree extensionCount stride count seed
    half extension

/-- The empty source gives the zero decoded output for every field seed. -/
theorem decodedCondenser_nil (s v : Nat)
    (halfDegree extensionCount stride count : List Bool)
    (seed : AdjoinRoot (binaryModulus s))
    (half : halfDegree.length = 3 ^ s) (extension : extensionCount.length = 3 ^ v) :
    decodedCondenser s halfDegree extensionCount stride count [] seed = 0 :=
  Internal.decodedCondenser_nil s v halfDegree extensionCount stride count seed half extension

end Algebraic.Cutwidth.Extractor
