/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.Encoding.Formula.Stream.Defs
public import Complexitylib.Circuits.Encoding.Formula.Stream.Internal

/-!
# Stack-free streams for finite Boolean folds

Finite conjunctions and disjunctions are right-associated formula trees, but
their exact raw compilation does not require a run-time formula stack. It is a
forward stream of member fragments, one identity constant, and a reverse stream
of connector gates. These identities are the proof interface used by the
log-space direct-unrolling serializer.

This module proves the exact proof-level list decomposition. The future
transducer will realize its reverse suffix with an indexed cursor and
recomputation; no executable cursor is claimed here.

## Main results

- `BoolFormula.compileRaw_conjs_eq_rightFold` gives the exact conjunction stream.
- `BoolFormula.compileRaw_disjs_eq_rightFold` gives the exact disjunction stream.
- `BoolFormula.length_compileRawRightFold` gives its exact gate count.
-/

@[expose] public section

namespace Complexity

namespace BoolFormula

@[simp] theorem rightFoldSize_nil : rightFoldSize [] = 1 :=
  rightFoldSize_nil_internal

@[simp] theorem rightFoldSize_cons
    (formula : BoolFormula) (formulas : List BoolFormula) :
    rightFoldSize (formula :: formulas) =
      formula.size + rightFoldSize formulas + 1 :=
  rightFoldSize_cons_internal formula formulas

theorem rightFoldSize_eq_size_conjs (formulas : List BoolFormula) :
    rightFoldSize formulas = (conjs formulas).size :=
  rightFoldSize_eq_size_conjs_internal formulas

theorem rightFoldSize_eq_size_disjs (formulas : List BoolFormula) :
    rightFoldSize formulas = (disjs formulas).size :=
  rightFoldSize_eq_size_disjs_internal formulas

/-- Exact raw compilation of a finite conjunction as a stack-free gate stream. -/
theorem compileRaw_conjs_eq_rightFold
    (available : ℕ) (formulas : List BoolFormula) :
    compileRaw available (conjs formulas) =
      compileRawRightFold .and true available formulas :=
  compileRaw_conjs_eq_rightFold_internal available formulas

/-- Exact raw compilation of a finite disjunction as a stack-free gate stream. -/
theorem compileRaw_disjs_eq_rightFold
    (available : ℕ) (formulas : List BoolFormula) :
    compileRaw available (disjs formulas) =
      compileRawRightFold .or false available formulas :=
  compileRaw_disjs_eq_rightFold_internal available formulas

@[simp] theorem length_rightFoldConnectors (op : AndOrOp)
    (available : ℕ) (formulas : List BoolFormula) :
    (rightFoldConnectors op available formulas).length = formulas.length :=
  length_rightFoldConnectors_internal op available formulas

@[simp] theorem length_compileRawRightFold (op : AndOrOp)
    (identity : Bool) (available : ℕ) (formulas : List BoolFormula) :
    (compileRawRightFold op identity available formulas).length =
      rightFoldSize formulas :=
  length_compileRawRightFold_internal op identity available formulas

end BoolFormula

end Complexity
