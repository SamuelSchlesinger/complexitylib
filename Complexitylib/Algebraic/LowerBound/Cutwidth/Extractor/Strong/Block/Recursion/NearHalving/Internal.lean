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
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.NearHalving.Parameters
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Extraction
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Condenser.Identity
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Projection
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.OneShot.Weighted
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Encoding.Explicit.Pair
import Mathlib.Tactic.Convert
import Mathlib.Tactic.Positivity

/-!
# Instantiating the near-halving recursive extraction guarantee

The identity supplies the initial one-block source, and the actual paired
condensers satisfy the generic recursion's two entropy inequalities.
The leaf gap pays the final one-shot threshold. The existing dyadic error
sum retains all shared seeds and bounds the whole recursive program.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

variable [∀ s, Fintype (AdjoinRoot (binaryModulus s))]

theorem nearHalvingBlockExtractor_weighted (n h Q E : Nat)
    (capacity : nearHalvingBlockEntropy h Q 0 ≤ n)
    (budget : 12 * (nearHalvingBlockRate h + 1) *
      explicitCondenserBudget n (nearHalvingBlockEntropy h Q 0) E + 4 * E ≤ Q) :
    WeightedStrongSeededExtractor (nearHalvingBlockExtractor n h Q E)
      (2 ^ nearHalvingBlockEntropy h Q 0)
      ((3 * (2 : ℝ) ^ h - 1) * ((2 : ℝ) ^ E)⁻¹) := by
  have initial : WeightedStrongSeededCondenser
      (fun (x : Fin n → Bool) (_ : Unit) => x)
      (2 ^ nearHalvingBlockEntropy h Q 0) (2 ^ nearHalvingBlockEntropy h Q 0)
      (((2 : ℝ) ^ E)⁻¹) :=
    WeightedStrongSeededCondenser.id (by positivity)
  have leafReserve : nearHalvingBlockLeafLength h Q + 2 * E ≤
      nearHalvingBlockEntropy h Q h :=
    nearHalvingBlockLeafLength_budget h Q E (by lia)
  have leaf := (decodedOneShotExtractor_ofFn_weighted
    (nearHalvingBlockWidth n h Q E h) (nearHalvingBlockLeafLength h Q) E).mono_threshold
      (Nat.pow_le_pow_right (by decide : 0 < 2) leafReserve)
  have result := initial.recursiveExtractor
    (n := h) (k := nearHalvingBlockEntropy h Q)
    (m := fun i => nearHalvingBlockWidth n h Q E (i + 1))
    (e := fun _ => E) (ε := fun _ => ((2 : ℝ) ^ E)⁻¹)
    (nearHalvingBlockStep n h Q E)
    (fun i _ => explicitCondenserPair_weighted (nearHalvingBlockWidth n h Q E i)
      (nearHalvingBlockEntropy h Q i) E (nearHalvingBlockRate h)
      (by dsimp [nearHalvingBlockRate]; lia))
    (by intro i _; simp)
    (fun _ hi => (nearHalvingBlock_split_budget_of_bound
      n h Q E _ capacity le_rfl budget hi).1)
    (fun _ hi => (nearHalvingBlock_split_budget_of_bound
      n h Q E _ capacity le_rfl budget hi).2)
    leaf
  rw [recursiveBlockError_dyadic_total] at result
  convert result using 1
  rfl

theorem nearHalvingBlockExtractor_dyadic (n h Q e : Nat)
    (capacity : nearHalvingBlockEntropy h Q 0 ≤ n)
    (budget : 12 * (nearHalvingBlockRate h + 1) *
      explicitCondenserBudget n (nearHalvingBlockEntropy h Q 0) (e + h + 2) +
      4 * (e + h + 2) ≤ Q) :
    WeightedStrongSeededExtractor (nearHalvingBlockExtractor n h Q (e + h + 2))
      (2 ^ nearHalvingBlockEntropy h Q 0) (((2 : ℝ) ^ e)⁻¹) := by
  have result := nearHalvingBlockExtractor_weighted n h Q (e + h + 2) capacity budget
  intro p probability cap T
  exact (result p probability cap T).trans (recursiveBlockError_dyadic_budget h e)

end Algebraic.Cutwidth.Extractor.Internal
