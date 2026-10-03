/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.NearHalving.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Defs
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.NearHalving.Internal

/-!
# Strong extraction with near-halving entropy budgets

The actual recursively paired condensers, followed by shared one-shot leaf
extraction, form a strong extractor whenever the initial capacity and one
finite reserve inequality hold. The recurrence preserves at least seven
eighths of the initial entropy in the total output. Every seed is retained
in the joint statistical guarantee, including the final pair shared by all
leaves. An identity initialization spends no seed bits.

The condense/split method is from Chattopadhyay--Goodman--Liao, Theorem 5.6
of *Affine Extractors for Almost Logarithmic Entropy*:
<https://eccc.weizmann.ac.il/report/2021/075/>. This depth-dependent rate and
its conservative integer reserve are deductions for the present library.
The short-seed parameter choice and uniform evaluator are separate layers.
-/

public section

namespace Algebraic.Cutwidth.Extractor

/-- The specified map strongly extracts with its explicit full recursive error bound. -/
theorem nearHalvingBlockExtractor_weighted (n h Q E : Nat)
    [∀ s, Fintype (AdjoinRoot (binaryModulus s))]
    (capacity : nearHalvingBlockEntropy h Q 0 ≤ n)
    (budget : 12 * (nearHalvingBlockRate h + 1) *
      explicitCondenserBudget n (nearHalvingBlockEntropy h Q 0) E + 4 * E ≤ Q) :
    WeightedStrongSeededExtractor (nearHalvingBlockExtractor n h Q E)
      (2 ^ nearHalvingBlockEntropy h Q 0)
      ((3 * (2 : ℝ) ^ h - 1) * ((2 : ℝ) ^ E)⁻¹) :=
  Internal.nearHalvingBlockExtractor_weighted n h Q E capacity budget

/-- A common local exponent `e+h+2` pays for the complete recursion at error `2^(-e)`. -/
theorem nearHalvingBlockExtractor_dyadic (n h Q e : Nat)
    [∀ s, Fintype (AdjoinRoot (binaryModulus s))]
    (capacity : nearHalvingBlockEntropy h Q 0 ≤ n)
    (budget : 12 * (nearHalvingBlockRate h + 1) *
      explicitCondenserBudget n (nearHalvingBlockEntropy h Q 0) (e + h + 2) +
      4 * (e + h + 2) ≤ Q) :
    WeightedStrongSeededExtractor (nearHalvingBlockExtractor n h Q (e + h + 2))
      (2 ^ nearHalvingBlockEntropy h Q 0) (((2 : ℝ) ^ e)⁻¹) :=
  Internal.nearHalvingBlockExtractor_dyadic n h Q e capacity budget

end Algebraic.Cutwidth.Extractor
