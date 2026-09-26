/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.AC0.NormalForm

/-!
# Finite unbounded connectives

Public evaluation, size, and depth laws for list conjunctions and disjunctions.
Empty lists are included. These laws support compilation of finite quantifiers.
-/

public section

namespace Complexity.AC0Formula

/-- List conjunction evaluates by Boolean `all`. -/
theorem eval_andList (input : BitString N) (fs : List (AC0Formula N)) :
    (andList fs).eval input = fs.all (eval input) := evalAll_ofList_internal input fs

/-- List disjunction evaluates by Boolean `any`. -/
theorem eval_orList (input : BitString N) (fs : List (AC0Formula N)) :
    (orList fs).eval input = fs.any (eval input) := evalAny_ofList_internal input fs

/-- A conjunction adds one gate to the sum of child sizes. -/
theorem size_andList (fs : List (AC0Formula N)) :
    (andList fs).size = 1 + (fs.map size).sum := by
  exact congrArg (1 + ·) (forestSize_ofList_internal fs)

/-- A disjunction adds one gate to the sum of child sizes. -/
theorem size_orList (fs : List (AC0Formula N)) :
    (orList fs).size = 1 + (fs.map size).sum := by
  exact congrArg (1 + ·) (forestSize_ofList_internal fs)

/-- A uniform bound on child depths bounds their forest depth. -/
theorem forestDepth_ofList_le (fs : List (AC0Formula N)) (d : Nat)
    (h : ∀ f ∈ fs, f.depth ≤ d) : forestDepth (.ofList fs) ≤ d := by
  induction fs with
  | nil => simp [AC0Forest.ofList, forestDepth]
  | cons f fs ih =>
    simp only [AC0Forest.ofList, forestDepth]
    exact max_le (h f (by simp)) (ih (fun g hg => h g (by simp [hg])))

/-- List conjunction adds at most one layer to a common child-depth bound. -/
theorem depth_andList_le (fs : List (AC0Formula N)) (d : Nat)
    (h : ∀ f ∈ fs, f.depth ≤ d) : (andList fs).depth ≤ d + 1 := by
  simpa only [andList, depth, Nat.add_comm] using
    Nat.add_le_add_left (forestDepth_ofList_le fs d h) 1

/-- List disjunction adds at most one layer to a common child-depth bound. -/
theorem depth_orList_le (fs : List (AC0Formula N)) (d : Nat)
    (h : ∀ f ∈ fs, f.depth ≤ d) : (orList fs).depth ≤ d + 1 := by
  simpa only [orList, depth, Nat.add_comm] using
    Nat.add_le_add_left (forestDepth_ofList_le fs d h) 1

end Complexity.AC0Formula
