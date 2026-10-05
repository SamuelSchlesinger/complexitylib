/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Entropy.Pair.Internal

/-!
# Exact entropy cap for overlapping actual conjunction features

Each Boolean feature need only imply a signed conjunction on two primary
coordinates. It may include arbitrary predicates of all inputs, as actual
conjunction gates with internal predecessors do. If the primary pairs overlap,
the two features together cost at most the entropy of `(5/8, 1/8, 1/8, 1/8)`.

Constant false features are included. Consequently the saving over the two
quarter-biased marginal caps is not a mutual-information lower bound.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Aggregate.Geometry.Entropy

open scoped Classical

/-- Intersecting primary pairs bound the joint cost even with arbitrary extra predicates. -/
noncomputable def SignedEdge.dominatedPairWeightBound {V : Type*}
    [Fintype V] [DecidableEq V] (e f : SignedEdge V)
    (overlap : e.left = f.left ∨ e.left = f.right ∨
      e.right = f.left ∨ e.right = f.right)
    (first second : (V → Bool) → Bool)
    (hfirst : ∀ x, first x = true → e.eval x = true)
    (hsecond : ∀ x, second x = true → f.eval x = true) :
    WeightBound (fun x => (first x, second x)) pairEntropyCost := by
  by_cases h₁ : e.left = f.left
  · exact PairInternal.dominatedSharedLeft e f h₁ first second hfirst hsecond
  by_cases h₂ : e.left = f.right
  · exact PairInternal.dominatedSharedLeft e f.reverse h₂ first second hfirst
      (by simpa only [SignedEdge.eval_reverse] using hsecond)
  by_cases h₃ : e.right = f.left
  · exact PairInternal.dominatedSharedLeft e.reverse f h₃ first second
      (by simpa only [SignedEdge.eval_reverse] using hfirst) hsecond
  have h₄ := ((overlap.resolve_left h₁).resolve_left h₂).resolve_left h₃
  exact PairInternal.dominatedSharedLeft e.reverse f.reverse h₄ first second
    (by simpa only [SignedEdge.eval_reverse] using hfirst)
    (by simpa only [SignedEdge.eval_reverse] using hsecond)

/-- The joint cap is strictly smaller than two separate quarter-biased marginal caps. -/
theorem pairEntropySaving_pos : 0 < pairEntropySaving := by
  have bound : Real.log ((3 : ℝ) ^ 12) < Real.log ((2 : ℝ) ^ 8 * 5 ^ 5) :=
    Real.log_lt_log (by norm_num) (by norm_num)
  rw [Real.log_mul (by norm_num) (by norm_num), Real.log_pow, Real.log_pow,
    Real.log_pow] at bound
  norm_num only [Nat.cast_ofNat] at bound
  rw [pairEntropySaving, pairEntropyCost, binEntropy_quarter_eq]
  linarith

end Algebraic.Cutwidth.Aggregate.Geometry.Entropy
