/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Scheduled.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Defs
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Scheduled.Internal

/-!
# A fully specified finite recursive strong extractor

The initial condenser, all internal condensers, their actual rounded widths,
and the final one-shot extractor are specified by the numerical definitions.
The explicit reserve `4096*(L+E+1)` discharges every level's entropy budget.
The resulting map outputs `2^h` blocks of `L` field bits, with all seeds
retained in the statistical test.

The construction uses the recursive condensation and splitting method of
Chattopadhyay--Goodman--Liao, Theorem 5.6 of *Affine Extractors for Almost
Logarithmic Entropy*, <https://eccc.weizmann.ac.il/report/2021/075/>.
Our constant-rate schedule pays a factor of four in entropy per level;
it does not assert their sharper entropy bound. The seed-length estimate
and a uniform encoded evaluator are separate layers. Finite-field instances
are supplied by the proved cardinality of each binary quotient.
-/

public section

namespace Algebraic.Cutwidth.Extractor

variable [∀ s, Fintype (AdjoinRoot (binaryModulus s))]

/-- The specified component maps give strong extraction whenever one global
reserve budget and the final one-shot entropy requirement are satisfied. -/
theorem scheduledBlockExtractor_weighted (n h Q E ell : Nat)
    (budget : 3 * (24 * explicitCondenserBudget (scheduledBlockInitialWidth n h Q E)
      (recursiveBlockEntropy h Q 0) E) + 6 * E ≤ 2 * Q)
    (reserve : ell + 2 * E ≤ Q) :
    WeightedStrongSeededExtractor (scheduledBlockExtractor n h Q E ell)
      (2 ^ recursiveBlockEntropy h Q 0)
      ((3 * (2 : ℝ) ^ h - 1) * ((2 : ℝ) ^ E)⁻¹) :=
  Internal.scheduledBlockExtractor_weighted n h Q E ell budget reserve

/-- The explicit reserve and local exponent `e+h+2` give total error `2^(-e)`.
The only numerical premises bound the source logarithm and recursion depth. -/
theorem scheduledBlockExtractor_dyadic (n h L e : Nat)
    (length : Nat.clog 2 (n + 1) ≤ L) (depth : h ≤ L) :
    WeightedStrongSeededExtractor
      (scheduledBlockExtractor n h (recursiveBlockReserve L (e + h + 2)) (e + h + 2) L)
      (2 ^ recursiveBlockEntropy h (recursiveBlockReserve L (e + h + 2)) 0)
      (((2 : ℝ) ^ e)⁻¹) :=
  Internal.scheduledBlockExtractor_dyadic n h L e length depth

end Algebraic.Cutwidth.Extractor
