/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Fiber.Entropy.Internal

/-!
# Mixed entropy inequalities for the large-fiber lower bound

Scalar circuits retain both the marginal and shared-graph message estimates.
For permutations, constant conjunction-output messages cost zero; output rank
then gives two inequalities with the same narrow and wide gate counts.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Aggregate.Geometry.Fiber

open Algebraic.Aggregate.Geometry

/-- A logarithmic receiving side retains separate marginal narrow and wide savings. -/
theorem input_le_size_of_marginal_entropy {n K : ℕ} (c : Circuit signature n 1)
    (hK : 0 < K) (disperse : FlatSumsetDisperser (c.outputFunction interpretation 0) K)
    (range : Nat.clog 2 K + 4 ≤ n) :
    (n : ℝ) - Nat.clog 2 K - 1 ≤ c.size + 1 + Real.logb 2 K -
      Shared.receiverRetention n (Nat.clog 2 K) *
        (Entropy.bitSaving * (Algebraic.Aggregate.Geometry.Shared.exactTwo c.program).card +
          Shared.wideSaving * (Joint.retainedWide c.program Finset.univ).card) := by
  let k := Nat.clog 2 K
  let a := n - (k + 1)
  have ha : 3 ≤ a := by dsimp only [a, k]; lia
  have han : a ≤ n := Nat.sub_le _ _
  have complement : n - a = k + 1 := by dsimp only [a, k]; lia
  have large : 2 * K ≤ 2 ^ (n - a) := by
    rw [complement, Nat.pow_succ]
    have upper := Nat.le_pow_clog (by decide : 1 < 2) K
    dsimp only [k]
    lia
  have bound := input_le_size_of_triple_marginal c ha han hK disperse.rectangleFree
    (Geometry.disperse_not disperse).rectangleFree large
  have cast_a : (a : ℝ) = n - k - 1 := by
    dsimp only [a]
    rw [Nat.cast_sub (by dsimp only [k]; lia), Nat.cast_add, Nat.cast_one]
    ring
  have ratio : Joint.tripleRetention n a = Shared.receiverRetention n k := by
    unfold Joint.tripleRetention Shared.receiverRetention
    rw [cast_a]
    ring
  rw [ratio, cast_a] at bound
  exact bound

/-- Nonaffine permutation outputs combine with the separate marginal message savings. -/
theorem three_mul_input_add_marginal_le_two_mul_size {n : ℕ} (c : Circuit signature n n)
    (bijective : Function.Bijective (c.eval interpretation))
    (nonliteral : ∀ i j b, c.outputFunction interpretation i ≠ fun x => b ^^ x j)
    (independent : NonaffineComponents (c.eval interpretation)) :
    3 * (n : ℝ) +
        Entropy.bitSaving * (Algebraic.Aggregate.Geometry.Shared.exactTwo c.program).card +
        Shared.wideSaving * (Joint.retainedWide c.program Finset.univ).card ≤ 2 * c.size := by
  have rank := independent.output_le_conjunctionCount
  have outputs := input_add_conjunctionCount_le_size_add_outputConjunctionCount c bijective
    (by intro i j; simpa using nonliteral i j false)
  have information := permutation_input_le_message_cost c bijective nonliteral false
  have ranks : (n : ℝ) ≤ conjunctionCount c.program := by exact_mod_cast rank
  have counts : (n : ℝ) + conjunctionCount c.program ≤
      c.size + outputConjunctionCount c := by exact_mod_cast outputs
  simp only [Bool.false_eq_true, ↓reduceIte, sub_zero, one_mul] at information
  linarith

/-- Nonaffine permutation outputs also retain the joint support-graph savings. -/
theorem three_sub_penalty_mul_input_add_joint_le_two_mul_size {n : ℕ}
    (c : Circuit signature n n) (bijective : Function.Bijective (c.eval interpretation))
    (nonliteral : ∀ i j b, c.outputFunction interpretation i ≠ fun x => b ^^ x j)
    (independent : NonaffineComponents (c.eval interpretation)) :
    (3 - Joint.overlapPenalty) * n +
        Joint.gateSaving * (Algebraic.Aggregate.Geometry.Shared.exactTwo c.program).card +
        Shared.wideSaving * (Joint.retainedWide c.program Finset.univ).card ≤ 2 * c.size := by
  have rank := independent.output_le_conjunctionCount
  have outputs := input_add_conjunctionCount_le_size_add_outputConjunctionCount c bijective
    (by intro i j; simpa using nonliteral i j false)
  have information := permutation_input_le_message_cost c bijective nonliteral true
  have ranks : (n : ℝ) ≤ conjunctionCount c.program := by exact_mod_cast rank
  have counts : (n : ℝ) + conjunctionCount c.program ≤
      c.size + outputConjunctionCount c := by exact_mod_cast outputs
  simp only [↓reduceIte] at information
  linarith

end Algebraic.Cutwidth.Aggregate.Geometry.Fiber
