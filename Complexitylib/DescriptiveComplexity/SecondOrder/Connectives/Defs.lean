/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.DescriptiveComplexity.SecondOrder.Renaming

/-!
# Combining existential second-order prefixes

Pull the leading existential relation quantifiers of both operands outward,
weakening the other operand at each binder. Once both prefixes are exhausted,
join the matrices by conjunction or disjunction. This is the usual closure
construction for existential second-order logic, implemented on de Bruijn syntax.
-/

@[expose] public section

namespace Complexity.DescriptiveComplexity.SOFormula

/-- Merge leading existential SO prefixes, then combine their matrices.
`isConjunction = true` selects conjunction and `false` selects disjunction. -/
def mergeExist {V : Vocabulary} (isConjunction : Bool) :
    {rctx : List Nat} → {n : Nat} →
      SOFormula V rctx n → SOFormula V rctx n → SOFormula V rctx n
  | rctx, _, .soExist k φ, ψ =>
    .soExist k (mergeExist isConjunction φ (ψ.renameRel (RelRenaming.weaken rctx k)))
  | rctx, _, φ, .soExist k ψ =>
    .soExist k (mergeExist isConjunction (φ.renameRel (RelRenaming.weaken rctx k)) ψ)
  | _, _, φ, ψ => if isConjunction then .conj φ ψ else .disj φ ψ
termination_by _ _ φ ψ => φ.size + ψ.size
decreasing_by all_goals simp only [size_renameRel, size]; omega

/-- Conjoin existential SO formulas with their relation quantifiers in one prefix. -/
def existConj {V : Vocabulary} {rctx : List Nat} {n : Nat}
    (φ ψ : SOFormula V rctx n) : SOFormula V rctx n := mergeExist true φ ψ

/-- Disjoin existential SO formulas with their relation quantifiers in one prefix. -/
def existDisj {V : Vocabulary} {rctx : List Nat} {n : Nat}
    (φ ψ : SOFormula V rctx n) : SOFormula V rctx n := mergeExist false φ ψ

end Complexity.DescriptiveComplexity.SOFormula
