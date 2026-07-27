/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.AC0.NormalForm.Defs
public import Complexitylib.Circuits.AC0.NormalForm.Internal

/-!
# Negation-normal unbounded formulas for AC0

This public surface provides the semantic and quantitative De Morgan laws for
`AC0Formula`, the tree representation used by AC0 normalization and
restriction arguments.
-/

@[expose] public section

namespace Complexity
namespace AC0Formula

/-- De Morgan negation computes Boolean complement. -/
theorem eval_neg (input : BitString N) (formula : AC0Formula N) :
    formula.neg.eval input = !(formula.eval input) :=
  eval_neg_internal input formula

/-- Negation preserves total tree size. -/
theorem size_neg (formula : AC0Formula N) :
    formula.neg.size = formula.size :=
  size_neg_internal formula

/-- Negation preserves formula depth. -/
theorem depth_neg (formula : AC0Formula N) :
    formula.neg.depth = formula.depth :=
  depth_neg_internal formula

end AC0Formula
end Complexity
