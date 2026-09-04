/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.AC0.NormalForm.Defs

/-!
# Negation-normal unbounded formulas -- proof internals
-/


public section

namespace Complexity
namespace AC0Formula

mutual

theorem eval_neg_internal (input : BitString N)
    (formula : AC0Formula N) :
    formula.neg.eval input = !(formula.eval input) := by
  cases formula with
  | const value => rfl
  | lit literal => exact Literal.eval_neg literal input
  | and children => exact evalAny_negForest_internal input children
  | or children => exact evalAll_negForest_internal input children

theorem evalAny_negForest_internal (input : BitString N)
    (formulas : AC0Forest N) :
    evalAny input (negForest formulas) = !(evalAll input formulas) := by
  cases formulas with
  | nil => rfl
  | cons formula formulas =>
    rw [negForest, evalAny, evalAll, eval_neg_internal,
      evalAny_negForest_internal]
    cases formula.eval input <;> cases evalAll input formulas <;> rfl

theorem evalAll_negForest_internal (input : BitString N)
    (formulas : AC0Forest N) :
    evalAll input (negForest formulas) = !(evalAny input formulas) := by
  cases formulas with
  | nil => rfl
  | cons formula formulas =>
    rw [negForest, evalAll, evalAny, eval_neg_internal,
      evalAll_negForest_internal]
    cases formula.eval input <;> cases evalAny input formulas <;> rfl

end

mutual

theorem size_neg_internal (formula : AC0Formula N) :
    formula.neg.size = formula.size := by
  cases formula with
  | const value => rfl
  | lit literal => rfl
  | and children =>
      rw [neg, size, size, forestSize_negForest_internal]
  | or children =>
      rw [neg, size, size, forestSize_negForest_internal]

theorem forestSize_negForest_internal (formulas : AC0Forest N) :
    forestSize (negForest formulas) = forestSize formulas := by
  cases formulas with
  | nil => rfl
  | cons formula formulas =>
    rw [negForest, forestSize, forestSize, size_neg_internal,
      forestSize_negForest_internal]

end

mutual

theorem depth_neg_internal (formula : AC0Formula N) :
    formula.neg.depth = formula.depth := by
  cases formula with
  | const value => rfl
  | lit literal => rfl
  | and children =>
      rw [neg, depth, depth, forestDepth_negForest_internal]
  | or children =>
      rw [neg, depth, depth, forestDepth_negForest_internal]

theorem forestDepth_negForest_internal (formulas : AC0Forest N) :
    forestDepth (negForest formulas) = forestDepth formulas := by
  cases formulas with
  | nil => rfl
  | cons formula formulas =>
    rw [negForest, forestDepth, forestDepth, depth_neg_internal,
      forestDepth_negForest_internal]

end

theorem evalAll_ofList_internal (input : BitString N)
    (formulas : List (AC0Formula N)) :
    evalAll input (.ofList formulas) = formulas.all (eval input) := by
  induction formulas with
  | nil => rfl
  | cons formula formulas ih =>
      simp only [AC0Forest.ofList, evalAll, List.all_cons, ih]

theorem evalAny_ofList_internal (input : BitString N)
    (formulas : List (AC0Formula N)) :
    evalAny input (.ofList formulas) = formulas.any (eval input) := by
  induction formulas with
  | nil => rfl
  | cons formula formulas ih =>
      simp only [AC0Forest.ofList, evalAny, List.any_cons, ih]

theorem forestSize_ofList_internal (formulas : List (AC0Formula N)) :
    forestSize (.ofList formulas) = (formulas.map size).sum := by
  induction formulas with
  | nil => rfl
  | cons formula formulas ih =>
      simp only [AC0Forest.ofList, forestSize, List.map_cons,
        List.sum_cons, ih]

theorem forestGateCount_ofList_internal (formulas : List (AC0Formula N)) :
    forestGateCount (.ofList formulas) = (formulas.map gateCount).sum := by
  induction formulas with
  | nil => rfl
  | cons formula formulas ih =>
      simp only [AC0Forest.ofList, forestGateCount, List.map_cons,
        List.sum_cons, ih]

theorem forestDepth_ofList_internal (formulas : List (AC0Formula N)) :
    forestDepth (.ofList formulas) =
      formulas.foldr (fun formula rest => max formula.depth rest) 0 := by
  induction formulas with
  | nil => rfl
  | cons formula formulas ih =>
      simp only [AC0Forest.ofList, forestDepth, List.foldr_cons, ih]

end AC0Formula
end Complexity
