/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.AC0.NormalForm
public import Complexitylib.Circuits.Restriction
import Std.Tactic.BVDecide.Normalize.Bool
import Std.Tactic.BVDecide.Normalize.Prop

/-!
# Restricting negation-normal AC0 formulas

Finite-arity restrictions substitute fixed literals by constants while
retaining the unbounded connective tree. Evaluation commutes with this
operation, tree size and depth are preserved exactly, and variable support is
filtered to the free variables.
-/

@[expose] public section

namespace Complexity
namespace AC0Formula

mutual

/-- Apply a finite-arity restriction to an AC0 formula. -/
def restrict (restriction : Restriction.On N) :
    AC0Formula N → AC0Formula N
  | .const value => .const value
  | .lit literal =>
      match restriction literal.var with
      | none => .lit literal
      | some value =>
          .const (if literal.polarity then value else !value)
  | .and children => .and (restrictForest restriction children)
  | .or children => .or (restrictForest restriction children)

/-- Apply a restriction to every formula in a forest. -/
def restrictForest (restriction : Restriction.On N) :
    AC0Forest N → AC0Forest N
  | .nil => .nil
  | .cons formula formulas =>
      .cons (restrict restriction formula)
        (restrictForest restriction formulas)

end

mutual

/-- Evaluation commutes with restricting an AC0 formula. -/
theorem eval_restrict (restriction : Restriction.On N)
    (input : BitString N) (formula : AC0Formula N) :
    (restrict restriction formula).eval input =
      formula.eval (restriction.applyTo input) := by
  cases formula with
  | const value => rfl
  | lit literal =>
      cases hvalue : restriction literal.var with
      | none =>
          simp [restrict, eval, Literal.eval,
            Restriction.On.applyTo, hvalue]
      | some value =>
          cases literal.polarity <;> cases value <;>
            simp [restrict, eval, Literal.eval,
              Restriction.On.applyTo, hvalue]
  | and children =>
      exact evalAll_restrictForest restriction input children
  | or children =>
      exact evalAny_restrictForest restriction input children

/-- Conjunctive forest evaluation commutes with restriction. -/
theorem evalAll_restrictForest (restriction : Restriction.On N)
    (input : BitString N) (formulas : AC0Forest N) :
    evalAll input (restrictForest restriction formulas) =
      evalAll (restriction.applyTo input) formulas := by
  cases formulas with
  | nil => rfl
  | cons formula formulas =>
    rw [restrictForest, evalAll, evalAll, eval_restrict,
      evalAll_restrictForest]

/-- Disjunctive forest evaluation commutes with restriction. -/
theorem evalAny_restrictForest (restriction : Restriction.On N)
    (input : BitString N) (formulas : AC0Forest N) :
    evalAny input (restrictForest restriction formulas) =
      evalAny (restriction.applyTo input) formulas := by
  cases formulas with
  | nil => rfl
  | cons formula formulas =>
    rw [restrictForest, evalAny, evalAny, eval_restrict,
      evalAny_restrictForest]

end

mutual

/-- Restriction preserves total syntax-tree size exactly. -/
theorem size_restrict (restriction : Restriction.On N)
    (formula : AC0Formula N) :
    (restrict restriction formula).size = formula.size := by
  cases formula with
  | const value => rfl
  | lit literal =>
      cases hvalue : restriction literal.var with
      | none => simp [restrict, size, hvalue]
      | some value =>
          cases literal.polarity <;> cases value <;>
            simp [restrict, size, hvalue]
  | and children =>
      rw [restrict, size, size, forestSize_restrictForest]
  | or children =>
      rw [restrict, size, size, forestSize_restrictForest]

/-- Restriction preserves total forest size exactly. -/
theorem forestSize_restrictForest (restriction : Restriction.On N)
    (formulas : AC0Forest N) :
    forestSize (restrictForest restriction formulas) =
      forestSize formulas := by
  cases formulas with
  | nil => rfl
  | cons formula formulas =>
    rw [restrictForest, forestSize, forestSize,
      size_restrict, forestSize_restrictForest]

end

mutual

/-- Restriction preserves connective depth exactly. -/
theorem depth_restrict (restriction : Restriction.On N)
    (formula : AC0Formula N) :
    (restrict restriction formula).depth = formula.depth := by
  cases formula with
  | const value => rfl
  | lit literal =>
      cases hvalue : restriction literal.var with
      | none => simp [restrict, depth, hvalue]
      | some value =>
          cases literal.polarity <;> cases value <;>
            simp [restrict, depth, hvalue]
  | and children =>
      rw [restrict, depth, depth, forestDepth_restrictForest]
  | or children =>
      rw [restrict, depth, depth, forestDepth_restrictForest]

/-- Restriction preserves maximum forest depth exactly. -/
theorem forestDepth_restrictForest (restriction : Restriction.On N)
    (formulas : AC0Forest N) :
    forestDepth (restrictForest restriction formulas) =
      forestDepth formulas := by
  cases formulas with
  | nil => rfl
  | cons formula formulas =>
    rw [restrictForest, forestDepth, forestDepth,
      depth_restrict, forestDepth_restrictForest]

end

mutual

/-- Restriction removes exactly the variables it fixes. -/
theorem vars_restrict (restriction : Restriction.On N)
    (formula : AC0Formula N) :
    (restrict restriction formula).vars =
      formula.vars.filter fun index =>
        restriction index = none := by
  cases formula with
  | const value => simp [restrict, vars]
  | lit literal =>
      cases hvalue : restriction literal.var with
      | none =>
          ext index
          simp [restrict, vars, hvalue]
          intro hindex
          subst index
          exact hvalue
      | some value =>
          cases literal.polarity <;> ext index <;>
            simp [restrict, vars, hvalue]
          all_goals
            intro hindex
            subst index
            simp [hvalue]
  | and children =>
      rw [restrict, vars, vars, forestVars_restrictForest]
  | or children =>
      rw [restrict, vars, vars, forestVars_restrictForest]

/-- Forest support is filtered to the free variables by restriction. -/
theorem forestVars_restrictForest (restriction : Restriction.On N)
    (formulas : AC0Forest N) :
    forestVars (restrictForest restriction formulas) =
      (forestVars formulas).filter fun index =>
        restriction index = none := by
  cases formulas with
  | nil => simp [restrictForest, forestVars]
  | cons formula formulas =>
    rw [restrictForest, forestVars, forestVars, vars_restrict,
      forestVars_restrictForest, Finset.filter_union]

end

end AC0Formula
end Complexity
