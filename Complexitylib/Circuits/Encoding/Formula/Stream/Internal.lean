/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.Encoding.Formula.Batch
public import Complexitylib.Circuits.Encoding.Formula.Stream.Defs

/-!
# Stack-free streams for finite Boolean folds — proof internals
-/

@[expose] public section

namespace Complexity

namespace BoolFormula

theorem rightFoldSize_nil_internal :
    rightFoldSize [] = 1 := by
  simp [rightFoldSize]

theorem rightFoldSize_cons_internal
    (formula : BoolFormula) (formulas : List BoolFormula) :
    rightFoldSize (formula :: formulas) =
      formula.size + rightFoldSize formulas + 1 := by
  simp [rightFoldSize]
  omega

theorem rightFoldSize_eq_size_conjs_internal (formulas : List BoolFormula) :
    rightFoldSize formulas = (conjs formulas).size := by
  simp [rightFoldSize]

theorem rightFoldSize_eq_size_disjs_internal (formulas : List BoolFormula) :
    rightFoldSize formulas = (disjs formulas).size := by
  simp [rightFoldSize]

theorem compileRaw_conjs_eq_rightFold_internal
    (available : ℕ) (formulas : List BoolFormula) :
    compileRaw available (conjs formulas) =
      compileRawRightFold .and true available formulas := by
  induction formulas generalizing available with
  | nil => simp [conjs, compileRaw, compileRawRightFold, compileRawOutputs,
      rightFoldConnectors]
  | cons formula formulas ih =>
      simp only [conjs, compileRaw, compileRawRightFold, compileRawOutputs,
        rightFoldConnectors]
      rw [ih]
      simp only [compileRawRightFold, rightFoldSize_eq_size_conjs_internal]
      simp [rawOutputWire, List.append_assoc]

theorem compileRaw_disjs_eq_rightFold_internal
    (available : ℕ) (formulas : List BoolFormula) :
    compileRaw available (disjs formulas) =
      compileRawRightFold .or false available formulas := by
  induction formulas generalizing available with
  | nil => simp [disjs, compileRaw, compileRawRightFold, compileRawOutputs,
      rightFoldConnectors]
  | cons formula formulas ih =>
      simp only [disjs, compileRaw, compileRawRightFold, compileRawOutputs,
        rightFoldConnectors]
      rw [ih]
      simp only [compileRawRightFold, rightFoldSize_eq_size_disjs_internal]
      simp [rawOutputWire, List.append_assoc]

theorem length_rightFoldConnectors_internal (op : AndOrOp)
    (available : ℕ) (formulas : List BoolFormula) :
    (rightFoldConnectors op available formulas).length = formulas.length := by
  induction formulas generalizing available with
  | nil => simp [rightFoldConnectors]
  | cons formula formulas ih =>
      simp [rightFoldConnectors, ih]

theorem length_compileRawRightFold_internal (op : AndOrOp)
    (identity : Bool) (available : ℕ) (formulas : List BoolFormula) :
    (compileRawRightFold op identity available formulas).length =
      rightFoldSize formulas := by
  simp [compileRawRightFold, rightFoldSize,
    length_rightFoldConnectors_internal]
  omega

end BoolFormula

end Complexity
