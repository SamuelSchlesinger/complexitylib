/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.Shallow.Layer.Defs
public import Complexitylib.Cslib.Circuit.Depth
public import Mathlib.Data.List.OfFn
public import Mathlib.Algebra.BigOperators.Fin

/-!
# Proofs and CSLib compilation for alternating layers

Parallel subcircuits retain their depths. The combining gate consumes signed
outputs directly, so primary-input negations require no separate gate layer.
-/

public section

namespace Complexity.Shallow.Layer

open Cslib.Circuits

theorem size_mapInputs {n m d : ℕ} (ρ : Fin n → Fin m × Bool) (f : Layer n d) :
    size (mapInputs ρ f) = size f := by
  induction d with
  | zero => rfl
  | succ d ih => simp [size, mapInputs, List.map_map, Function.comp_def, ih]

theorem eval_mapInputs {n m d : ℕ} (ρ : Fin n → Fin m × Bool) (f : Layer n d)
    (op : AndOrOp) (x : BitString m) :
    eval op (mapInputs ρ f) x = eval op f (fun i => (ρ i).2.xor (x (ρ i).1)) := by
  induction d generalizing op with
  | zero => exact Bool.xor_assoc ..
  | succ d ih =>
    cases op <;> simp [eval, mapInputs, List.all_map, List.any_map, Function.comp_def, ih]

theorem eval_neg {n d : ℕ} (f : Layer n d) (op : AndOrOp) (x : BitString n) :
    eval op.dual (neg f) x = !(eval op f x) := by
  induction d generalizing op with
  | zero => simp [neg, mapInputs, eval]
  | succ d ih =>
    have hn : neg f = f.map neg := rfl
    have ha (g : Layer n d) : eval .and (neg g) x = !(eval .or g x) := ih g .or
    have ho (g : Layer n d) : eval .or (neg g) x = !(eval .and g x) := ih g .and
    cases op <;> simp [hn, AndOrOp.dual, eval, List.all_map, List.any_map,
      Function.comp_def, List.not_all_eq_any_not, List.not_any_eq_all_not, ha, ho]

private theorem parallel {n m : ℕ}
    (cs : Fin m → Cslib.Circuits.Circuit Basis.unboundedAndOr.signature n 1) (d : ℕ)
    (hd : ∀ i, (cs i).depth ≤ d) (hn : ∀ i, InputNegationsOnly (cs i)) :
    ∃ c : Cslib.Circuits.Circuit Basis.unboundedAndOr.signature n m,
      c.size = ∑ i, (cs i).size ∧ c.depth ≤ d ∧
        (∀ x i, c.eval Basis.unboundedAndOr.interpretation x i =
          (cs i).eval Basis.unboundedAndOr.interpretation x 0) ∧ InputNegationsOnly c := by
  induction m with
  | zero =>
    refine ⟨.wiring _ Fin.elim0, ?_, ?_, ?_, trivial⟩
    · simp
    · simp
    · intro x i; exact i.elim0
  | succ m ih =>
    obtain ⟨c, hs, hc, he, hn'⟩ := ih (fun i => cs i.castSucc)
      (fun i => hd i.castSucc) (fun i => hn i.castSucc)
    refine ⟨c.append (cs (Fin.last m)), ?_, c.depth_append_le _ d hc (hd _), ?_,
      hn'.append (hn _)⟩
    · simp [hs, Fin.sum_univ_castSucc]
    · intro x i
      induction i using Fin.lastCases with
      | last =>
        rw [Cslib.Circuits.Circuit.eval_append]
        exact Fin.append_right _ _ (0 : Fin 1)
      | cast i =>
        rw [Cslib.Circuits.Circuit.eval_append]
        exact (Fin.append_left _ _ i).trans (he x i)

private def combine {n m : ℕ}
    (c : Cslib.Circuits.Circuit Basis.unboundedAndOr.signature n m)
    (op : AndOrOp) (sign : BitString m) :
    Cslib.Circuits.Circuit Basis.unboundedAndOr.signature n 1 :=
  ⟨c.program.gate ⟨⟨op, m, by cases op <;> trivial, sign⟩, c.outputs⟩,
    fun _ => .gate (Fin.last c.size)⟩

private theorem eval_combine {n m : ℕ}
    (c : Cslib.Circuits.Circuit Basis.unboundedAndOr.signature n m)
    (op : AndOrOp) (sign : BitString m) (x : BitString n) :
    (combine c op sign).eval Basis.unboundedAndOr.interpretation x 0 =
      op.eval m (fun i => (sign i).xor (c.eval Basis.unboundedAndOr.interpretation x i)) := by
  simp only [combine, Cslib.Circuits.Circuit.eval, Program.trace, Program.eval,
    Function.comp_apply, Fin.lastCases_last,
    Wire.elim, Line.eval, Basis.interpretation, Basis.unboundedAndOr]
  rfl

private theorem depth_combine {n m : ℕ}
    (c : Cslib.Circuits.Circuit Basis.unboundedAndOr.signature n m)
    (op : AndOrOp) (sign : BitString m) (d : ℕ) (hd : c.depth ≤ d) :
    (combine c op sign).depth ≤ d + 1 := by
  rw [Cslib.Circuits.Circuit.depth_le_iff]
  intro i
  simp only [combine, Cslib.Circuits.Circuit.outputDepths, Function.comp_apply,
    Program.wireDepths_gate_last]
  apply Nat.succ_le_succ
  exact Algebraic.Fin.foldl_max_le _ _ _ (Nat.zero_le _)
    ((c.depth_le_iff d).1 hd)

private theorem eval_get {n d : ℕ} (op : AndOrOp) (fs : List (Layer n d))
    (x : BitString n) :
    op.eval fs.length (fun i => eval op.dual (fs.get i) x) =
      eval op (d := d + 1) fs x := by
  have ha {α : Type} (ys : List α) (p : α → Bool) (b : Bool) :
      Fin.foldl ys.length (fun acc i => acc && p (ys.get i)) b = (b && ys.all p) := by
    induction ys generalizing b with
    | nil => simp [Fin.foldl_zero]
    | cons y ys ih =>
      change Fin.foldl ys.length (fun acc i => acc && p (ys.get i)) (b && p y) = _
      rw [ih]
      simp [Bool.and_assoc]
  have ho {α : Type} (ys : List α) (p : α → Bool) (b : Bool) :
      Fin.foldl ys.length (fun acc i => acc || p (ys.get i)) b = (b || ys.any p) := by
    induction ys generalizing b with
    | nil => simp [Fin.foldl_zero]
    | cons y ys ih =>
      change Fin.foldl ys.length (fun acc i => acc || p (ys.get i)) (b || p y) = _
      rw [ih]
      simp [Bool.or_assoc]
  cases op with
  | and =>
    simpa only [eval, AndOrOp.eval, AndOrOp.dual, Bool.true_and] using
      (ha fs (fun f => eval .or f x) true)
  | or =>
    simpa only [eval, AndOrOp.eval, AndOrOp.dual, Bool.false_or] using
      (ho fs (fun f => eval .and f x) false)

theorem exists_signed_circuit {n d : ℕ} (f : Layer n d) (op : AndOrOp) :
    ∃ (c : Cslib.Circuits.Circuit Basis.unboundedAndOr.signature n 1) (b : Bool),
      c.size = size f ∧ c.depth ≤ d ∧
      (∀ x, b.xor (c.eval Basis.unboundedAndOr.interpretation x 0) = eval op f x) ∧
      (0 < d → b = false) ∧ InputNegationsOnly c := by
  classical
  induction d generalizing op with
  | zero =>
    exact ⟨.wiring _ (fun _ => f.1), f.2, rfl, by simp, fun _ => rfl, by omega, trivial⟩
  | succ d ih =>
    choose cs bs hs hd he hb hn using fun i : Fin f.length => ih (f.get i) op.dual
    obtain ⟨c, hc, hcd, hce, hcn⟩ := parallel cs d hd hn
    refine ⟨combine c op bs, false, ?_, depth_combine c op bs d hcd, ?_,
      fun _ => rfl, ?_⟩
    · change c.size + 1 = 1 + (f.map size).sum
      rw [hc]
      simp only [hs]
      have hsum : (∑ i : Fin f.length, size (f.get i)) = (f.map size).sum := by
        induction f with
        | nil => simp
        | cons a fs _ => simp [Fin.sum_univ_succ]
      omega
    · intro x
      rw [Bool.false_xor, eval_combine]
      simp only [hce, he]
      exact eval_get op f x
    · refine ⟨hcn, fun i hi => ?_⟩
      change bs i = true at hi
      cases d with
      | zero =>
        have hc0 : c.size = 0 := by simp [hc, hs, size]
        cases hw : c.outputs i with
        | input j => exact ⟨j, hw⟩
        | gate j => have := j.isLt; omega
      | succ d => simp [hb i (by omega)] at hi

end Complexity.Shallow.Layer
