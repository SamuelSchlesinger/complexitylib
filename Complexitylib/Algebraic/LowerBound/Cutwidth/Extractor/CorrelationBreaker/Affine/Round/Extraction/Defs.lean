/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.Round.Final.Defs

/-!
# Explicit error of one actual subset-union round

Four extractor errors and two previous-row discrepancies accumulate through
the actual round. The remaining charges come from the first right seed,
merging the nearly uniform old row, recovering the final right seed, and
rereading the original left source. Counts `s` and `u` are the first subset
size and the union size; `leftMass` and `rightMass` are the totals of the
original source envelopes.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Extractor

/-- The four actual calls' error, with all observed-message and tampered-output charges explicit. -/
noncomputable def affineRoundError (t h L e s u : Nat) (ρS ρT leftMass rightMass : ℝ) : ℝ :=
  4 * ((2 : ℝ) ^ e)⁻¹ + ρS + ρT +
    (2 : ℝ) ^ (2 ^ 62 * L + (s + t + 1) * matchedBlockSeedBits L) * rightMass +
    (2 : ℝ) ^ (2 ^ 62 * L + (s + t + 1) * matchedBlockSeedBits L) /
      (2 : ℝ) ^ matchedBlockOutputBits h L +
    (2 : ℝ) ^ (2 ^ 62 * L + (u + 3 * (t + 1)) * matchedBlockSeedBits L) * rightMass +
    (2 : ℝ) ^ (2 ^ (2 * h + 14) * L + u * matchedBlockOutputBits h L +
      2 * (t + 1) * matchedBlockSeedBits L) * leftMass

end Algebraic.Cutwidth.Extractor
