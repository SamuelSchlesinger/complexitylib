/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.OneShot.Defs

/-!
# Runtime one-shot extraction on blocks with shared seeds

Read `count.length` consecutive input blocks of width `n`, run the actual
one-shot extractor on each with the same condenser and hash seed words,
and concatenate the `ell`-bit outputs in block order. The count word's bit
values are irrelevant. Width, output length, and count may be zero; short
or extra payloads use the total fixed-width slicing convention.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Extractor

/-- Apply the actual one-shot extractor to each block, reusing both runtime seed words. -/
def oneShotBlockExtractorBits (n ell e : Nat)
    (blocks condenserSeed hashSeed count : List Bool) : List Bool :=
  (List.range count.length).flatMap fun j =>
    oneShotExtractorBits n ell e (Complexity.BitPolynomial.coefficientBlock blocks n j)
      condenserSeed hashSeed

end Algebraic.Cutwidth.Extractor
