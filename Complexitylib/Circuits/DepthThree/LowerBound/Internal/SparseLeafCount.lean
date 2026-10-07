/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.SparseStreams
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.Entropy
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Unrestricted depth-three lower bound: sparse leaf count

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DepthThree/SparseLeafCount.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical proofs are retained.
-/

@[expose] public section

namespace Complexity

universe uDepth1

namespace DepthThreeLowerBound

open scoped BigOperators

namespace SparseDecisionTree

variable {Label : Type uDepth1} [DecidableEq Label] [Fintype Label]

theorem card_le_entropy_sum (t : SparseDecisionTree Label) (N r : Label → ℕ)
    (hr : ∀ i, 2 ≤ r i)
    (hN : ∀ (p : t.Leaf) i, (t.stream p i).length ≤ N i)
    (hones : ∀ (p : t.Leaf) i, r i * (t.stream p i).count true ≤ N i) :
    (Fintype.card t.Leaf : ℝ) ≤
      (2 : ℝ) ^ (∑ i, (N i : ℝ) * binaryEntropy (1 / (r i : ℝ))) := by
  classical
  let admitted (i : Label) := sparseBinaryStrings (N i) (1 / (r i : ℝ))
  have hrpos (i : Label) : (0 : ℝ) < r i := by
    have htwo : (2 : ℝ) ≤ r i := by exact_mod_cast hr i
    linarith
  have hhalf (i : Label) : (1 : ℝ) / r i ≤ 1 / 2 := by
    apply (div_le_div_iff₀ (hrpos i) (by norm_num : (0 : ℝ) < 2)).mpr
    simpa only [one_mul] using (show (2 : ℝ) ≤ r i by exact_mod_cast hr i)
  have hmem : ∀ (p : t.Leaf) i, t.padded N p i ∈ admitted i := by
    intro p i
    have hcast : (r i : ℝ) * ((t.stream p i).count true : ℝ) ≤ N i := by
      exact_mod_cast hones p i
    have hbound : ((t.stream p i).count true : ℝ) ≤
        (N i : ℝ) * (1 / (r i : ℝ)) := by
      rw [mul_one_div]
      apply (le_div_iff₀ (hrpos i)).mpr
      simpa only [mul_comm] using hcast
    simp only [admitted, sparseBinaryStrings, Finset.mem_filter, Finset.mem_univ,
      true_and, t.padded_trueCount N p i (hN p i)]
    exact hbound
  have hnat := t.card_le_prod_admitted N hN admitted hmem
  have hreal : (Fintype.card t.Leaf : ℝ) ≤ ∏ i, ((admitted i).card : ℝ) := by
    exact_mod_cast hnat
  calc
    (Fintype.card t.Leaf : ℝ) ≤ ∏ i, ((admitted i).card : ℝ) := hreal
    _ ≤ ∏ i, (2 : ℝ) ^ ((N i : ℝ) * binaryEntropy (1 / (r i : ℝ))) := by
      apply Finset.prod_le_prod₀
      · intro i _
        exact Nat.cast_nonneg _
      · intro i _
        exact card_sparse_binary_strings_le (N i) (one_div_pos.mpr (hrpos i)) (hhalf i)
    _ = _ := (Real.rpow_sum_of_pos (by norm_num : (0 : ℝ) < 2)
      (fun i => (N i : ℝ) * binaryEntropy (1 / (r i : ℝ))) Finset.univ).symm

theorem card_le_of_entropy_budget (t : SparseDecisionTree Label) (N r : Label → ℕ)
    (hr : ∀ i, 2 ≤ r i)
    (hN : ∀ (p : t.Leaf) i, (t.stream p i).length ≤ N i)
    (hones : ∀ (p : t.Leaf) i, r i * (t.stream p i).count true ≤ N i)
    {B : ℝ} (hbudget : (∑ i, (N i : ℝ) * binaryEntropy (1 / (r i : ℝ))) ≤ B) :
    (Fintype.card t.Leaf : ℝ) ≤ (2 : ℝ) ^ B :=
  (t.card_le_entropy_sum N r hr hN hones).trans
    (Real.rpow_le_rpow_of_exponent_le (by norm_num) hbudget)

end SparseDecisionTree

end DepthThreeLowerBound

end Complexity
