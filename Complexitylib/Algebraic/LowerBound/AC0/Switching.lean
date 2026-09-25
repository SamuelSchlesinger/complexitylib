/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.AC0.Switching.CombinedCanonical
public import Complexitylib.Algebraic.LowerBound.AC0.Duality

/-!
# The semantic switching lemma

This module exposes the representation-independent consequence of the
canonical DNF switching injection. For a width-`t` DNF under the independent
`p`-random restriction, the probability that the restricted Boolean function
has decision-tree depth at least `s` is at most `(5pt)^s`.

The event concerns every decision tree computing the restricted function. The
proof does not search for an optimal tree: semantic depth at least `s` forces
the explicitly constructed canonical tree to have depth at least `s`, after
which the canonical switching lemma applies.
-/

@[expose] public section

namespace Algebraic
namespace AC0
namespace RandomRestriction

open scoped ENNReal

/-- **Hastad's switching lemma, decision-tree form.** A width-`t` DNF left
under a `p`-random restriction has semantic decision-tree depth at least `s`
with probability at most `(5pt)^s`.

Here `DecisionTree.DepthAtLeast f s` means that every decision tree computing
`f` has depth at least `s`; in particular, threshold zero is the certain
event. -/
theorem probability_depthAtLeast_restrict_le_five
    (formula : DNF n)
    (bounded : formula.WidthAtMost widthBound)
    (pathLength : Nat)
    (p : NNReal)
    (atMostOne : p ≤ 1) :
    probability n p atMostOne
        (fun rho => DecisionTree.DepthAtLeast
          (formula.restrict rho).eval pathLength) ≤
      ((5 : ENNReal) * (p : ENNReal) * (widthBound : ENNReal)) ^
        pathLength := by
  calc
    probability n p atMostOne
          (fun rho => DecisionTree.DepthAtLeast
            (formula.restrict rho).eval pathLength) ≤
        probability n p atMostOne
          (fun rho => formula.CanonicalDepthAtLeast rho pathLength) :=
      probability_mono n p atMostOne fun rho lower =>
        formula.canonicalDepthAtLeast_of_depthAtLeast
          rho pathLength lower
    _ ≤ ((5 : ENNReal) * (p : ENNReal) *
          (widthBound : ENNReal)) ^ pathLength :=
      probability_canonicalDepthAtLeast_le_five
        formula bounded pathLength p atMostOne

/-- Equivalent off-by-one form: the probability that the restricted DNF has
no computing tree of depth at most `depthBound` is at most
`(5pt)^(depthBound + 1)`. -/
theorem probability_not_depthAtMost_restrict_le_five
    (formula : DNF n)
    (bounded : formula.WidthAtMost widthBound)
    (depthBound : Nat)
    (p : NNReal)
    (atMostOne : p ≤ 1) :
    probability n p atMostOne
        (fun rho => ¬DecisionTree.DepthAtMost
          (formula.restrict rho).eval depthBound) ≤
      ((5 : ENNReal) * (p : ENNReal) * (widthBound : ENNReal)) ^
        (depthBound + 1) := by
  simpa only [DecisionTree.depthAtLeast_succ_iff_not_depthAtMost] using
    probability_depthAtLeast_restrict_le_five
      formula bounded (depthBound + 1) p atMostOne

/-- **Hastad's switching lemma, CNF form.** A width-`t` CNF left under a
`p`-random restriction has semantic decision-tree depth at least `s` with
probability at most `(5pt)^s`. This is the exact De Morgan dual of the DNF
theorem. -/
theorem probability_cnf_depthAtLeast_restrict_le_five
    (formula : CNF n)
    (bounded : formula.WidthAtMost widthBound)
    (pathLength : Nat)
    (p : NNReal)
    (atMostOne : p ≤ 1) :
    probability n p atMostOne
        (fun rho => DecisionTree.DepthAtLeast
          (formula.restrict rho).eval pathLength) ≤
      ((5 : ENNReal) * (p : ENNReal) * (widthBound : ENNReal)) ^
        pathLength := by
  calc
    probability n p atMostOne
          (fun rho => DecisionTree.DepthAtLeast
            (formula.restrict rho).eval pathLength) =
        probability n p atMostOne
          (fun rho => DecisionTree.DepthAtLeast
            (formula.negate.restrict rho).eval pathLength) := by
      apply probability_congr n p atMostOne
      intro rho
      rw [← formula.negate_restrict rho]
      have evalEqual : (formula.restrict rho).negate.eval =
          fun input => !(formula.restrict rho).eval input := by
        funext input
        exact CNF.eval_negate (formula.restrict rho) input
      rw [evalEqual]
      exact
        (DecisionTree.depthAtLeast_negate_iff
          (formula.restrict rho).eval pathLength).symm
    _ ≤ ((5 : ENNReal) * (p : ENNReal) *
          (widthBound : ENNReal)) ^ pathLength :=
      probability_depthAtLeast_restrict_le_five
        formula.negate bounded.negate pathLength p atMostOne

/-- Equivalent off-by-one CNF form: failure to have a depth-`d` computing
tree has probability at most `(5pt)^(d + 1)`. -/
theorem probability_cnf_not_depthAtMost_restrict_le_five
    (formula : CNF n)
    (bounded : formula.WidthAtMost widthBound)
    (depthBound : Nat)
    (p : NNReal)
    (atMostOne : p ≤ 1) :
    probability n p atMostOne
        (fun rho => ¬DecisionTree.DepthAtMost
          (formula.restrict rho).eval depthBound) ≤
      ((5 : ENNReal) * (p : ENNReal) * (widthBound : ENNReal)) ^
        (depthBound + 1) := by
  simpa only [DecisionTree.depthAtLeast_succ_iff_not_depthAtMost] using
    probability_cnf_depthAtLeast_restrict_le_five
      formula bounded (depthBound + 1) p atMostOne

end RandomRestriction
end AC0
end Algebraic
