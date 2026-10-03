/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Encoding.Explicit.Pair.Defs

/-!
# A constant-rate numerical schedule for block recursion

The entropy budget decreases by a factor of four at each executed level.
Every internal condenser uses rate parameter three. Its actual output
half-width is the next block width, including all sparse-field rounding.
The initial width is supplied separately so the initial compression can use
its own rate and input length.

These total numerical definitions do not by themselves assert the entropy
inequalities, seed bound, or polynomial-time complexity of a recursive run.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Extractor

/-- Entropy retained at level `i` of a depth-`h` schedule with leaf reserve `Q`. -/
def recursiveBlockEntropy (h Q i : Nat) : Nat := 4 ^ (h - i) * Q

/-- Actual block widths after successive rate-three condensations and equal splits. -/
def recursiveBlockWidth (initial h Q E : Nat) : Nat → Nat
  | 0 => initial
  | i + 1 => explicitCondenserHalfWidth (recursiveBlockWidth initial h Q E i)
      (recursiveBlockEntropy h Q i) E 3

/-- Bit width of the fresh field seed at an internal level. -/
def recursiveBlockSeedWidth (initial h Q E i : Nat) : Nat :=
  sparseFieldBits 3 (explicitCondenserBudget (recursiveBlockWidth initial h Q E i)
    (recursiveBlockEntropy h Q i) E)

/-- A fixed leaf reserve large enough for the later explicit budget estimates. -/
def recursiveBlockReserve (L E : Nat) : Nat := 4096 * (L + E + 1)

end Algebraic.Cutwidth.Extractor
