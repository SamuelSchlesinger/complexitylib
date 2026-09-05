/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Classes.P.Composition
public import Complexitylib.Classes.P.PairWithInput
public import Complexitylib.Classes.P.UnaryLength
public import Complexitylib.Classes.PPoly.Uniform
public import Complexitylib.Classes.PPoly.Uniform.Preprocessing.Defs

/-!
# Inputs for uniform circuit-family evaluation — proof internals
-/


public section

namespace Complexity

/-- Internal polynomial-time construction of the serialized evaluator input. -/
theorem generatorEvalInput_mem_FP_internal {gen : List Bool → List Bool}
    (hgen : gen ∈ FP) : generatorEvalInput gen ∈ FP := by
  have hunary : (fun x : List Bool => unaryList x.length) ∈ FP := by
    simpa only [unaryList] using unaryLength_mem_FP
  have hcode : (fun x : List Bool => gen (unaryList x.length)) ∈ FP := by
    exact mem_FP_comp hunary hgen
  exact mem_FP_pairWithInput hcode

end Complexity
