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
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Scheduled.Internal.Components
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Parameters
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Parameters.Explicit
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Extraction
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Encoding.Explicit.Pair.Splitting
import Mathlib.Tactic.Convert

/-!
# Strong extraction with the actual constant-rate schedule

Instantiate the finite recursion with the initial rate-one condenser, the
actual rate-three level maps, and the final one-shot extractor. The explicit
reserve theorem discharges every entropy budget using only the chosen depth
and an upper bound on the original source length's binary logarithm.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

variable [∀ s, Fintype (AdjoinRoot (binaryModulus s))]

theorem scheduledBlockExtractor_weighted (n h Q E ell : Nat)
    (budget : 3 * (24 * explicitCondenserBudget (scheduledBlockInitialWidth n h Q E)
      (recursiveBlockEntropy h Q 0) E) + 6 * E ≤ 2 * Q)
    (reserve : ell + 2 * E ≤ Q) :
    WeightedStrongSeededExtractor (scheduledBlockExtractor n h Q E ell)
      (2 ^ recursiveBlockEntropy h Q 0)
      ((3 * (2 : ℝ) ^ h - 1) * ((2 : ℝ) ^ E)⁻¹) := by
  have capacity : recursiveBlockEntropy h Q 0 ≤ scheduledBlockInitialWidth n h Q E :=
    explicitCondenserHalfWidth_capacity n (recursiveBlockEntropy h Q 0) E (by decide)
  have result := (scheduledBlockInitial_weighted n h Q E).recursiveExtractor
    (n := h)
    (k := recursiveBlockEntropy h Q)
    (m := fun i => recursiveBlockWidth (scheduledBlockInitialWidth n h Q E) h Q E (i + 1))
    (e := fun _ => E) (ε := fun _ => ((2 : ℝ) ^ E)⁻¹)
    (scheduledBlockStep n h Q E)
    (fun i _ => scheduledBlockStep_weighted n h Q E i)
    (by intro i _; simp)
    (fun _ hi => (recursiveBlock_split_budget _ h Q E capacity budget hi).1)
    (fun _ hi => (recursiveBlock_split_budget _ h Q E capacity budget hi).2)
    (scheduledBlockLeaf_weighted _ h Q E ell reserve)
  rw [recursiveBlockError_dyadic_total] at result
  convert result using 1
  rfl

theorem scheduledBlockExtractor_dyadic (n h L e : Nat)
    (length : Nat.clog 2 (n + 1) ≤ L) (depth : h ≤ L) :
    WeightedStrongSeededExtractor
      (scheduledBlockExtractor n h (recursiveBlockReserve L (e + h + 2)) (e + h + 2) L)
      (2 ^ recursiveBlockEntropy h (recursiveBlockReserve L (e + h + 2)) 0)
      (((2 : ℝ) ^ e)⁻¹) := by
  have budget := recursiveBlockReserve_budget n L (e + h + 2) h length depth
  have reserve : L + 2 * (e + h + 2) ≤ recursiveBlockReserve L (e + h + 2) := by
    simp only [recursiveBlockReserve]
    lia
  have result := scheduledBlockExtractor_weighted n h
    (recursiveBlockReserve L (e + h + 2)) (e + h + 2) L budget reserve
  intro p probability cap T
  exact (result p probability cap T).trans (recursiveBlockError_dyadic_budget h e)

end Algebraic.Cutwidth.Extractor.Internal
