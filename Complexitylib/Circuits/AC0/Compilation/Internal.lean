/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.AC0.Compilation.Defs
public import Complexitylib.Circuits.AC0.NormalForm.Connectives
public import Complexitylib.Circuits.Composition

/-!
# Compiling unbounded formula trees to circuit DAGs

Pack child circuits in parallel and add one connective gate. Parallel packing
retains a common depth bound and sums sizes exactly; serial composition adds the
single parent gate. Constants and literals supply the base cases.
-/

public section

namespace Complexity.AC0Formula

variable {N : Nat} [NeZero N]

theorem constantCircuit_eval (value : Bool) (input : BitString N) :
    ((constantCircuit value).eval input) 0 = value := by
  cases value <;> rfl

theorem literalCircuit_eval (literal : Literal N) (input : BitString N) :
    ((literalCircuit literal).eval input) 0 = literal.eval input := by
  simp [literalCircuit, Circuit.eval, Gate.eval, Basis.unboundedAndOr, AndOrOp.eval,
    Fin.foldl_succ_last, Fin.foldl_zero, Circuit.wireValue_of_lt, Literal.eval]
  cases literal.polarity <;> simp

theorem connectiveCircuit_eval (op : AndOrOp) (input : BitString N) :
    ((connectiveCircuit op).eval input) 0 = op.eval N input := by
  simp [connectiveCircuit, Circuit.eval, Gate.eval, Basis.unboundedAndOr,
    Circuit.wireValue_of_lt]

theorem depth_no_internal {B : Basis} (c : Circuit B N 1 0) : c.depth = 1 := by
  simp [Circuit.depth, Circuit.outputDepth, Fin.foldl_succ_last, Fin.foldl_zero,
    Circuit.wireDepth_of_lt]
  generalize (c.outputs 0).fanIn = k
  induction k <;> simp [Fin.foldl_succ_last, Fin.foldl_zero, *]

omit [NeZero N] in
theorem size_le_forestSize_of_mem (f : AC0Formula N) (fs : AC0Forest N)
    (h : f ∈ fs.toList) : f.size ≤ forestSize fs := by
  cases fs with
  | nil => simp [AC0Forest.toList] at h
  | cons g gs =>
    simp only [AC0Forest.toList, List.mem_cons] at h
    rcases h with rfl | h
    · exact Nat.le_add_right _ _
    · exact (size_le_forestSize_of_mem f gs h).trans (Nat.le_add_left _ _)

private theorem foldl_and_get {α : Type} (xs : List α) (p : α → Bool) (b : Bool) :
    Fin.foldl xs.length (fun acc i => acc && p (xs.get i)) b = (b && xs.all p) := by
  induction xs generalizing b with
  | nil => simp [Fin.foldl_zero]
  | cons x xs ih =>
    change Fin.foldl xs.length (fun acc i => acc && p (xs.get i)) (b && p x) = _
    rw [ih]
    simp only [List.all_cons, Bool.and_assoc]

private theorem foldl_or_get {α : Type} (xs : List α) (p : α → Bool) (b : Bool) :
    Fin.foldl xs.length (fun acc i => acc || p (xs.get i)) b = (b || xs.any p) := by
  induction xs generalizing b with
  | nil => simp [Fin.foldl_zero]
  | cons x xs ih =>
    change Fin.foldl xs.length (fun acc i => acc || p (xs.get i)) (b || p x) = _
    rw [ih]
    simp only [List.any_cons, Bool.or_assoc]

omit [NeZero N] in
private theorem eval_ofOp_get (op : AndOrOp) (fs : AC0Forest N) (input : BitString N) :
    op.eval fs.toList.length (fun i => (fs.toList.get i).eval input) =
      (ofOp op fs).eval input := by
  cases op with
  | and => simpa only [AndOrOp.eval, foldl_and_get, Bool.true_and, ofOp, eval,
      AC0Forest.ofList_toList] using (evalAll_ofList_internal input fs.toList).symm
  | or => simpa only [AndOrOp.eval, foldl_or_get, Bool.false_or, ofOp, eval,
      AC0Forest.ofList_toList] using (evalAny_ofList_internal input fs.toList).symm

omit [NeZero N] in
private theorem sum_sizes (fs : AC0Forest N) :
    (∑ i : Fin fs.toList.length, (fs.toList.get i).size) = forestSize fs := by
  rw [← List.sum_ofFn]
  simpa only [List.get_eq_getElem, List.ofFn_getElem_eq_map, AC0Forest.ofList_toList] using
    (forestSize_ofList_internal fs.toList).symm

private theorem exists_connective (op : AndOrOp) (fs : AC0Forest N)
    (h : ∀ f ∈ fs.toList, ∃ gates, ∃ c : Circuit Basis.unboundedAndOr N 1 gates,
      c.size = f.size ∧ c.depth ≤ f.depth + 1 ∧
        ∀ input, c.eval input 0 = f.eval input) :
    ∃ gates, ∃ c : Circuit Basis.unboundedAndOr N 1 gates,
      c.size = (ofOp op fs).size ∧ c.depth ≤ (ofOp op fs).depth + 1 ∧
        ∀ input, c.eval input 0 = (ofOp op fs).eval input := by
  cases fs with
  | nil =>
    cases op
    · refine ⟨0, constantCircuit true, rfl, ?_, fun input => constantCircuit_eval true input⟩
      simp only [depth_no_internal, ofOp, depth, forestDepth]
      omega
    · refine ⟨0, constantCircuit false, rfl, ?_, fun input => constantCircuit_eval false input⟩
      simp only [depth_no_internal, ofOp, depth, forestDepth]
      omega
  | cons f fs =>
    let children := (AC0Forest.cons f fs).toList
    let : NeZero children.length := ⟨by simp [children, AC0Forest.toList]⟩
    choose gates circuits hsize hdepth heval using
      fun i : Fin children.length => h (children.get i) (List.get_mem children i)
    have hdepth' (i : Fin children.length) :
        (circuits i).depth ≤ forestDepth (.cons f fs) + 1 :=
      (hdepth i).trans (Nat.add_le_add_right
        (depth_le_forestDepth_of_mem _ (.cons f fs) (List.get_mem children i)) 1)
    obtain ⟨count, packed, hpackedSize, hpackedDepth, hpackedEval⟩ :=
      Circuit.exists_parallelFamily_depth (fun i => ⟨gates i, circuits i⟩) _ hdepth'
    refine ⟨_, (connectiveCircuit op).compose packed, ?_, ?_, ?_⟩
    · rw [Circuit.size_compose, hpackedSize]
      simp only [hsize]
      change (∑ i : Fin children.length, (children.get i).size) + 1 = _
      rw [show (∑ i : Fin children.length, (children.get i).size) =
        forestSize (.cons f fs) from sum_sizes _]
      cases op <;> simp only [ofOp, size, Nat.add_comm]
    · refine (Circuit.depth_compose_le _ _).trans ?_
      rw [depth_no_internal]
      cases op <;> simp only [ofOp, depth] <;> omega
    · intro input
      rw [Circuit.eval_compose, connectiveCircuit_eval]
      have hp : packed.eval input = fun i => (children.get i).eval input :=
        funext (fun i => (hpackedEval input i).trans (heval i input))
      rw [hp]
      exact eval_ofOp_get op (.cons f fs) input

theorem exists_circuit_internal (f : AC0Formula N) :
    ∃ gates, ∃ c : Circuit Basis.unboundedAndOr N 1 gates,
      c.size = f.size ∧ c.depth ≤ f.depth + 1 ∧
        ∀ input, c.eval input 0 = f.eval input := by
  induction hs : f.size using Nat.strong_induction_on generalizing f with
  | h s ih =>
    cases f with
    | const value =>
      refine ⟨0, constantCircuit value, hs, ?_, fun input => constantCircuit_eval value input⟩
      simp only [depth_no_internal, depth, Nat.zero_add, le_refl]
    | lit literal =>
      refine ⟨0, literalCircuit literal, hs, ?_, fun input => literalCircuit_eval literal input⟩
      simp only [depth_no_internal, depth, Nat.zero_add, le_refl]
    | and fs =>
      rw [← hs]
      apply exists_connective .and fs
      intro g hg
      apply ih g.size ?_ g rfl
      have := size_le_forestSize_of_mem g fs hg
      simp only [size] at hs
      omega
    | or fs =>
      rw [← hs]
      apply exists_connective .or fs
      intro g hg
      apply ih g.size ?_ g rfl
      have := size_le_forestSize_of_mem g fs hg
      simp only [size] at hs
      omega

end Complexity.AC0Formula
