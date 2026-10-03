/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Encoding.Explicit.Defs

/-!
# One runtime level of shared-seed block condensation

Read fixed-width input blocks from one flat word, apply the scheduled
condenser to each with the same seed, and concatenate the outputs in order.
The count word's length specifies the number of blocks. Its bit values are
irrelevant; extra input bits are ignored and short slices remain valid inputs
to the total underlying program. Width zero and count zero are allowed.

This is one block-processing level, not a variable-depth recursive evaluator.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Extractor

/-- Run the actual scheduled condenser on every fixed-width block with one shared seed. -/
def explicitBlockCondenserBits (n k e u : Nat)
    (blocks seed count : List Bool) : List Bool :=
  (List.range count.length).flatMap fun j =>
    explicitCondenserBits n k e u (Complexity.BitPolynomial.coefficientBlock blocks n j) seed

end Algebraic.Cutwidth.Extractor
