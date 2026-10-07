/-
Copyright (c) 2026 OpenAI, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Samuel Schlesinger
-/

module
public import Complexitylib.BooleanAnalysis.Sensitivity.Internal.QuerySeparation

/-!
# Sensitivity, block sensitivity, and decision-tree lower bounds

The source separation is OpenAI's 2026 formalization:
https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Sensitivity/Separation.lean

Here sensitivity is the maximum number of sensitive coordinates at one input,
not average sensitivity or Fourier total influence. Block sensitivity counts
pairwise disjoint nonempty blocks whose flips change the output.

The source constructs finite nonconstant functions with block sensitivity larger
than every constant multiple of squared sensitivity, and a family with a fixed
power separation above exponent two. The decision-tree consequences below use
complexitylib's existing `DecisionTree.On` model and its query depth. These are
checked deductions; no claim is made that they were unknown to the source authors.
-/

public section

namespace Complexity.BooleanAnalysis.Sensitivity
open DecisionTree

/-- Singleton blocks show that ordinary sensitivity never exceeds block sensitivity at an input. -/
theorem sensitivityAt_le_blockSensitivityAt {I : Type} [Fintype I]
    (f : (I → Bool) → Bool) (x : I → Bool) :
    sensitivityAt f x ≤ blockSensitivityAt f x :=
  Internal.sensitivityAt_le_blockSensitivityAt f x

/-- Maximum sensitivity never exceeds maximum block sensitivity. -/
theorem sensitivity_le_blockSensitivity {I : Type} [Fintype I]
    (f : (I → Bool) → Bool) : sensitivity f ≤ blockSensitivity f :=
  Internal.sensitivity_le_blockSensitivity f

/-- Every finite Boolean function has an exact decision tree of depth at most its arity. -/
theorem exists_decisionTree {n : ℕ} (f : BitString n → Bool) :
    ∃ tree : On n, (∀ x, tree.eval x = f x) ∧ tree.depth ≤ n :=
  Internal.exists_decisionTree f

/-- Every exact decision tree must query at least the block sensitivity in the worst case. -/
theorem blockSensitivity_le_depth {n : ℕ} (f : BitString n → Bool) (tree : On n)
    (heval : ∀ x, tree.eval x = f x) : blockSensitivity f ≤ tree.depth :=
  Internal.blockSensitivity_le_depth f tree heval

/-- The block sensitivity of a Boolean function is at most its input arity. -/
theorem blockSensitivity_le_arity {n : ℕ} (f : BitString n → Bool) :
    blockSensitivity f ≤ n :=
  Internal.blockSensitivity_le_arity f

/-- OpenAI's quantitative superquadratic separation between block sensitivity and sensitivity. -/
theorem quantitative_separation (d : ℕ) (hd : 1 ≤ d) :
    ∃ (n : ℕ) (f : (Fin n → Bool) → Bool),
      0 < n ∧ f (fun _ => false) = false ∧
      (∃ x y : Fin n → Bool, f x ≠ f y) ∧
      (2 : ℝ) ^ d / (4 * ((d : ℝ) + 2) ^ 2) ≤
        (blockSensitivity f : ℝ) / (sensitivity f : ℝ) ^ 2 :=
  Internal.quantitative_separation d hd

/-- No constant multiple of squared sensitivity bounds block sensitivity for all Boolean
functions. -/
theorem unbounded_quadratic_separation (C : ℝ) (hC : 0 < C) :
    ∃ (n : ℕ) (f : (Fin n → Bool) → Bool),
      0 < n ∧ f (fun _ => false) = false ∧
      (∃ x y : Fin n → Bool, f x ≠ f y) ∧
      C * (sensitivity f : ℝ) ^ 2 < (blockSensitivity f : ℝ) :=
  Internal.unbounded_quadratic_separation C hC

/-- OpenAI's fixed-power separation, with block sensitivity at zero tending to infinity. -/
theorem fixed_power_separation :
    ∃ α : ℝ, 2 < α ∧
      ∃ (n : ℕ → ℕ) (F : ∀ m : ℕ, (Fin (n m) → Bool) → Bool),
        (∀ m : ℕ, 1 ≤ m →
          0 < n m ∧ F m (fun _ => false) = false ∧
          (∃ x y : Fin (n m) → Bool, F m x ≠ F m y) ∧
          (sensitivity (F m) : ℝ) ^ α ≤
            (blockSensitivityAt (F m) (fun _ => false) : ℝ)) ∧
        Filter.Tendsto
          (fun m : ℕ => (blockSensitivityAt (F m) (fun _ => false) : ℝ))
          Filter.atTop Filter.atTop :=
  Internal.fixed_power_separation

/-- No constant multiple of squared sensitivity bounds the depth needed by exact decision trees. -/
theorem unbounded_quadratic_query_separation (C : ℝ) (hC : 0 < C) :
    ∃ (n : ℕ) (f : BitString n → Bool),
      0 < n ∧ f (fun _ => false) = false ∧
      (∃ x y, f x ≠ f y) ∧
      ∀ tree : On n, (∀ x, tree.eval x = f x) →
        C * (sensitivity f : ℝ) ^ 2 < (tree.depth : ℝ) :=
  Internal.unbounded_quadratic_query_separation C hC

/-- A fixed exponent above two separates sensitivity from exact query depth.
Every choice of exact trees for the family has unbounded depth. -/
theorem fixed_power_query_separation :
    ∃ α : ℝ, 2 < α ∧
      ∃ (n : ℕ → ℕ) (F : ∀ m : ℕ, BitString (n m) → Bool),
        (∀ m : ℕ, 1 ≤ m →
          0 < n m ∧ F m (fun _ => false) = false ∧
          (∃ x y, F m x ≠ F m y) ∧
          ∀ tree : On (n m), (∀ x, tree.eval x = F m x) →
            (sensitivity (F m) : ℝ) ^ α ≤ (tree.depth : ℝ)) ∧
        ∀ trees : (m : ℕ) → On (n m),
          (∀ m x, (trees m).eval x = F m x) →
          Filter.Tendsto (fun m => ((trees m).depth : ℝ)) Filter.atTop Filter.atTop :=
  Internal.fixed_power_query_separation

end Complexity.BooleanAnalysis.Sensitivity
