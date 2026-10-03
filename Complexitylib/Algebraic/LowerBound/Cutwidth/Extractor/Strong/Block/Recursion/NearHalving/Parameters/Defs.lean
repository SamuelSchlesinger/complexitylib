/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Encoding.Explicit.Pair.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.OneShot.Parameters.Defs

/-!
# A block schedule that retains nearly half the entropy at each split

The rate parameter depends on the total depth. Each next width is the actual
paired condenser half-width, including sparse rounding. The entropy gap pays
for both the field width and the splitting error. The initial block has the
supplied width, with no preliminary compression. One final seed pair is
shared by all leaves and counted once.

These total numerical definitions assert no splitting guarantee, asymptotic
parameter choice, or runtime bound. Their finite bounds are proved separately.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Extractor

/-- Rate parameter shared by all condensers at a fixed recursion depth. -/
def nearHalvingBlockRate (h : Nat) : Nat := 16 * (h + 1)

/-- Entropy at level `i`, including the reserve lost in each remaining split. -/
def nearHalvingBlockEntropy (h Q i : Nat) : Nat :=
  2 ^ (h - i) * (8 * h + 8 + (h - i)) * Q

/-- Actual rounded block widths after successive condensations and equal splits. -/
def nearHalvingBlockWidth (N h Q E : Nat) : Nat → Nat
  | 0 => N
  | i + 1 => explicitCondenserHalfWidth (nearHalvingBlockWidth N h Q E i)
      (nearHalvingBlockEntropy h Q i) E (nearHalvingBlockRate h)

/-- Bit width of the field seed used at one internal level. -/
def nearHalvingBlockSeedWidth (N h Q E i : Nat) : Nat :=
  sparseFieldBits (nearHalvingBlockRate h) (explicitCondenserBudget
    (nearHalvingBlockWidth N h Q E i) (nearHalvingBlockEntropy h Q i) E)

/-- Number of bits extracted from each final block. -/
def nearHalvingBlockLeafLength (h Q : Nat) : Nat := (8 * h + 7) * Q

/-- Number of bits in all final output blocks together. -/
def nearHalvingBlockOutputBits (h Q : Nat) : Nat :=
  2 ^ h * nearHalvingBlockLeafLength h Q

/-- Total width of internal field seeds and the final pair shared by all leaves. -/
def nearHalvingBlockSeedBits (N h Q E : Nat) : Nat :=
  let width := nearHalvingBlockWidth N h Q E h
  let ell := nearHalvingBlockLeafLength h Q
  (Finset.range h).sum (nearHalvingBlockSeedWidth N h Q E) +
    (2 * 3 ^ oneShotCondenserExponent width ell E + 2 * 3 ^ oneShotHashExponent width ell E)

end Algebraic.Cutwidth.Extractor
