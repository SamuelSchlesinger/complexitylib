/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.AC0.Switching

/-!
# Finite-family switching corollaries

Depth reduction must simplify every formula at a circuit layer, not just one
formula. The exact finite union bound lifts the DNF and CNF switching lemmas to
an indexed family: the probability that any of `M` width-`t` formulas retains
decision-tree depth at least `s` is at most `M * (5pt)^s`.

This is the ordinary union-bound corollary of the single-formula switching
lemma. It is intentionally not called a multi-switching lemma, whose conclusion
would provide one common shallow decision tree for an entire family.
-/

@[expose] public section

namespace Algebraic
namespace AC0
namespace RandomRestriction

open scoped BigOperators ENNReal

/-- Finite-family DNF switching bound obtained by a union bound. -/
theorem probability_exists_dnf_depthAtLeast_restrict_le_five
    (formulas : Fin formulaCount -> DNF n)
    (bounded : forall index, (formulas index).WidthAtMost widthBound)
    (pathLength : Nat)
    (p : NNReal)
    (atMostOne : p ≤ 1) :
    probability n p atMostOne
        (fun rho => ∃ index, DecisionTree.DepthAtLeast
          ((formulas index).restrict rho).eval pathLength) ≤
      (formulaCount : ENNReal) *
        (((5 : ENNReal) * (p : ENNReal) * (widthBound : ENNReal)) ^
          pathLength) := by
  let event (index : Fin formulaCount) (rho : PartialAssignment n) : Prop :=
    DecisionTree.DepthAtLeast
      ((formulas index).restrict rho).eval pathLength
  calc
    probability n p atMostOne (fun rho => ∃ index, event index rho) ≤
        ∑ index : Fin formulaCount,
          probability n p atMostOne (event index) := by
      simpa using probability_exists_mem_le_sum n p atMostOne
        Finset.univ event
    _ ≤ ∑ _index : Fin formulaCount,
          ((5 : ENNReal) * (p : ENNReal) *
            (widthBound : ENNReal)) ^ pathLength := by
      apply Finset.sum_le_sum
      intro index _
      exact probability_depthAtLeast_restrict_le_five
        (formulas index) (bounded index) pathLength p atMostOne
    _ = (formulaCount : ENNReal) *
          (((5 : ENNReal) * (p : ENNReal) *
            (widthBound : ENNReal)) ^ pathLength) := by
      simp

/-- Off-by-one finite-family DNF form used to obtain a simultaneous depth
upper bound. -/
theorem probability_exists_dnf_not_depthAtMost_restrict_le_five
    (formulas : Fin formulaCount -> DNF n)
    (bounded : forall index, (formulas index).WidthAtMost widthBound)
    (depthBound : Nat)
    (p : NNReal)
    (atMostOne : p ≤ 1) :
    probability n p atMostOne
        (fun rho => ∃ index, ¬DecisionTree.DepthAtMost
          ((formulas index).restrict rho).eval depthBound) ≤
      (formulaCount : ENNReal) *
        (((5 : ENNReal) * (p : ENNReal) * (widthBound : ENNReal)) ^
          (depthBound + 1)) := by
  simpa only [DecisionTree.depthAtLeast_succ_iff_not_depthAtMost] using
    probability_exists_dnf_depthAtLeast_restrict_le_five
      formulas bounded (depthBound + 1) p atMostOne

/-- Finite-family CNF switching bound obtained by De Morgan duality and a
union bound. -/
theorem probability_exists_cnf_depthAtLeast_restrict_le_five
    (formulas : Fin formulaCount -> CNF n)
    (bounded : forall index, (formulas index).WidthAtMost widthBound)
    (pathLength : Nat)
    (p : NNReal)
    (atMostOne : p ≤ 1) :
    probability n p atMostOne
        (fun rho => ∃ index, DecisionTree.DepthAtLeast
          ((formulas index).restrict rho).eval pathLength) ≤
      (formulaCount : ENNReal) *
        (((5 : ENNReal) * (p : ENNReal) * (widthBound : ENNReal)) ^
          pathLength) := by
  let event (index : Fin formulaCount) (rho : PartialAssignment n) : Prop :=
    DecisionTree.DepthAtLeast
      ((formulas index).restrict rho).eval pathLength
  calc
    probability n p atMostOne (fun rho => ∃ index, event index rho) ≤
        ∑ index : Fin formulaCount,
          probability n p atMostOne (event index) := by
      simpa using probability_exists_mem_le_sum n p atMostOne
        Finset.univ event
    _ ≤ ∑ _index : Fin formulaCount,
          ((5 : ENNReal) * (p : ENNReal) *
            (widthBound : ENNReal)) ^ pathLength := by
      apply Finset.sum_le_sum
      intro index _
      exact probability_cnf_depthAtLeast_restrict_le_five
        (formulas index) (bounded index) pathLength p atMostOne
    _ = (formulaCount : ENNReal) *
          (((5 : ENNReal) * (p : ENNReal) *
            (widthBound : ENNReal)) ^ pathLength) := by
      simp

/-- Off-by-one finite-family CNF form used to obtain a simultaneous depth
upper bound. -/
theorem probability_exists_cnf_not_depthAtMost_restrict_le_five
    (formulas : Fin formulaCount -> CNF n)
    (bounded : forall index, (formulas index).WidthAtMost widthBound)
    (depthBound : Nat)
    (p : NNReal)
    (atMostOne : p ≤ 1) :
    probability n p atMostOne
        (fun rho => ∃ index, ¬DecisionTree.DepthAtMost
          ((formulas index).restrict rho).eval depthBound) ≤
      (formulaCount : ENNReal) *
        (((5 : ENNReal) * (p : ENNReal) * (widthBound : ENNReal)) ^
          (depthBound + 1)) := by
  simpa only [DecisionTree.depthAtLeast_succ_iff_not_depthAtMost] using
    probability_exists_cnf_depthAtLeast_restrict_le_five
      formulas bounded (depthBound + 1) p atMostOne

end RandomRestriction
end AC0
end Algebraic
