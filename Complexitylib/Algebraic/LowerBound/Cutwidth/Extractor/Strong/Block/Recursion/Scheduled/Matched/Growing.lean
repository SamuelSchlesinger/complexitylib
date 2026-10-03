/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Scheduled.Matched.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Defs
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Scheduled.Matched.Growing.Internal

/-!
# Actual matched extraction at growing recursion depth

An explicit arithmetic budget lets the existing matched Boolean program
use arbitrary recursion depths. The complete retained seed still has
`2^24 * L` bits, the output has `2^h * L` bits, and the error is `2^(-e)`.
The input source entropy need only be `2^(2*h+14) * L` bits. As with the
fixed-depth theorem, an actual normalized source must fit that entropy
threshold; the numerical guard alone does not assert source capacity.

These conservative finite deductions support the alternating widths in
Chattopadhyay--Liao, *Extractors for Sum of Two Sources*, Theorem 6.1,
<https://arxiv.org/pdf/2110.12652>. They use the scheduled extractor already
constructed by the library and do not assert a complete affine correlation
breaker or change the existing fixed-depth runtime guard.
-/

public section

namespace Algebraic.Cutwidth.Extractor

/-- Paying the depth-error-logarithm product fits the actual seed in the fixed padded width. -/
theorem matchedBlockExtractor_growing_seedBits_le (n h L e : Nat)
    (length : Nat.clog 2 (n + 1) ≤ L)
    (error : e + h + 2 ≤ L)
    (budget : (h + 1) * (e + 2 * h + Nat.clog 2 (L + 1) + 4) ≤ L) :
    scheduledBlockSeedBits n h (recursiveBlockReserve L (e + h + 2))
      (e + h + 2) L ≤ matchedBlockSeedBits L :=
  Internal.matchedBlockExtractor_growing_seedBits_le n h L e length error budget

/-- The entropy exponent is quadratic in the power-of-two output factor. -/
theorem recursiveBlockEntropy_growing_le (h L e : Nat)
    (positive : 1 ≤ L) (error : e + h + 2 ≤ L) :
    recursiveBlockEntropy h (recursiveBlockReserve L (e + h + 2)) 0 ≤
      2 ^ (2 * h + 14) * L :=
  Internal.recursiveBlockEntropy_growing_le h L e positive error

/-- The exact scheduled entropy threshold works for every depth satisfying the seed budget. -/
theorem matchedBlockExtractor_growing_weighted (n h L e : Nat)
    (length : Nat.clog 2 (n + 1) ≤ L)
    (error : e + h + 2 ≤ L)
    (budget : (h + 1) * (e + 2 * h + Nat.clog 2 (L + 1) + 4) ≤ L) :
    WeightedStrongSeededExtractor (matchedBlockExtractor n h L e)
      (2 ^ recursiveBlockEntropy h (recursiveBlockReserve L (e + h + 2)) 0)
      (((2 : ℝ) ^ e)⁻¹) :=
  Internal.matchedBlockExtractor_growing_weighted n h L e length error budget

/-- A simple entropy reserve gives the same actual program's strong guarantee at any depth. -/
theorem matchedBlockExtractor_growing (n h L e : Nat)
    (length : Nat.clog 2 (n + 1) ≤ L)
    (error : e + h + 2 ≤ L)
    (budget : (h + 1) * (e + 2 * h + Nat.clog 2 (L + 1) + 4) ≤ L) :
    WeightedStrongSeededExtractor (matchedBlockExtractor n h L e)
      (2 ^ (2 ^ (2 * h + 14) * L)) (((2 : ℝ) ^ e)⁻¹) :=
  Internal.matchedBlockExtractor_growing n h L e length error budget

/-- Logarithmic depth supplies the middle extractor's reserve and all prefix/output leakage. -/
theorem matchedBlockOutputBits_merging_reserve (t L e : Nat) (error : e ≤ L) :
    2 ^ 62 * L + (2 * t + 2) * matchedBlockSeedBits L + e ≤
      matchedBlockOutputBits (Nat.clog 2 (t + 1) + 64) L :=
  Internal.matchedBlockOutputBits_merging_reserve t L e error

end Algebraic.Cutwidth.Extractor
