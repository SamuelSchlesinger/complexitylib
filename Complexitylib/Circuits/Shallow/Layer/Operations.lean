/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.Shallow.Layer
public import Mathlib.Data.Bool.Basic
public import Mathlib.Data.Fintype.Pi

/-!
# Finite connectives and depth-two synthesis

Constructing a new root adds one layer. Merging roots of the same kind uses
list flattening and preserves depth. Every Boolean function has depth-two
layers with at most `2^n + 1` gates, including at input length zero.
-/

@[expose] public section

namespace Complexity.Shallow.Layer

open Finset

/-- One root gate over a finite family of child layers. -/
noncomputable def gate {n d : ℕ} {ι : Type*} [Fintype ι]
    (fs : ι → Layer n d) : Layer n (d + 1) := univ.toList.map fs

theorem size_gate {n d : ℕ} {ι : Type*} [Fintype ι] (fs : ι → Layer n d) :
    size (gate fs) = 1 + ∑ i, size (fs i) := by
  simp [gate, size, List.map_map, Finset.sum_map_toList, Function.comp_def]

theorem eval_gate_and {n d : ℕ} {ι : Type*} [Fintype ι]
    (fs : ι → Layer n d) (x : BitString n) :
    eval .and (gate fs) x = true ↔ ∀ i, eval .or (fs i) x = true := by
  simp [gate, eval, List.all_map, List.all_eq_true, Function.comp_def]

theorem eval_gate_or {n d : ℕ} {ι : Type*} [Fintype ι]
    (fs : ι → Layer n d) (x : BitString n) :
    eval .or (gate fs) x = true ↔ ∃ i, eval .and (fs i) x = true := by
  simp [gate, eval, List.any_map, List.any_eq_true, Function.comp_def]

/-- Merge a finite collection of roots without adding a layer. -/
noncomputable def merge {n d : ℕ} {ι : Type*} [Fintype ι]
    (fs : ι → Layer n (d + 1)) : Layer n (d + 1) := (univ.toList.map fs).flatten

theorem eval_merge_and {n d : ℕ} {ι : Type*} [Fintype ι]
    (fs : ι → Layer n (d + 1)) (x : BitString n) :
    eval .and (merge fs) x = true ↔ ∀ i, eval .and (fs i) x = true := by
  simp [merge, eval, List.all_flatten, List.all_map, List.all_eq_true,
    Function.comp_def]

theorem eval_merge_or {n d : ℕ} {ι : Type*} [Fintype ι]
    (fs : ι → Layer n (d + 1)) (x : BitString n) :
    eval .or (merge fs) x = true ↔ ∃ i, eval .or (fs i) x = true := by
  simp [merge, eval, List.any_flatten, List.any_map, List.any_eq_true,
    Function.comp_def]

theorem size_merge_le {n d : ℕ} {ι : Type*} [Fintype ι]
    (fs : ι → Layer n (d + 1)) : size (merge fs) ≤ 1 + ∑ i, size (fs i) := by
  have h (ls : List (Layer n (d + 1))) :
      size (d := d + 1) ls.flatten ≤ 1 + (ls.map size).sum := by
    induction ls with
    | nil => simp [size]
    | cons f ls ih =>
      simp only [List.flatten_cons, size, List.map_append, List.sum_append,
        List.map_cons, List.sum_cons] at *
      omega
  simpa [merge, List.map_map, Function.comp_def, Finset.sum_map_toList] using
    h (univ.toList.map fs)

/-- A constant represented at any depth at least two. -/
def constant (n d : ℕ) (op : AndOrOp) (b : Bool) : Layer n (d + 2) :=
  if b = decide (op = .and) then [] else [[]]

theorem eval_constant (n d : ℕ) (op : AndOrOp) (b : Bool) (x : BitString n) :
    eval op (constant n d op b) x = b := by
  cases op <;> cases b <;> simp [constant, eval]

theorem size_constant_le (n d : ℕ) (op : AndOrOp) (b : Bool) :
    size (constant n d op b) ≤ 2 := by
  cases op <;> cases b <;> simp [constant, size]

/-- A clause excluding precisely one assignment. -/
noncomputable def excludingClause {n : ℕ} (y : BitString n) : Layer n 1 :=
  gate (fun i : Fin n => (i, y i))

theorem eval_excludingClause {n : ℕ} (y x : BitString n) :
    eval .or (excludingClause y) x = true ↔ x ≠ y := by
  rw [excludingClause, eval_gate_or]
  simp only [eval, Bool.xor_iff_ne]
  constructor
  · rintro ⟨i, hi⟩ h
    exact hi (congrFun h i).symm
  · intro h
    by_contra he
    apply h
    funext i
    have he' : ∀ i, y i = x i := by simpa only [not_exists, not_not] using he
    exact (he' i).symm

theorem size_excludingClause {n : ℕ} (y : BitString n) : size (excludingClause y) = 1 := by
  rw [excludingClause, size_gate]
  simp [size]

/-- Truth-table CNF, used only at the bottom of the depth induction. -/
noncomputable def cnf {n : ℕ} (f : BitString n → Bool) : Layer n 2 :=
  gate (fun y : {y : BitString n // f y = false} => excludingClause y.1)

theorem eval_cnf {n : ℕ} (f : BitString n → Bool) (x : BitString n) :
    eval .and (cnf f) x = f x := by
  apply Bool.eq_iff_iff.2
  rw [cnf, eval_gate_and]
  simp only [eval_excludingClause]
  constructor
  · intro h
    cases hf : f x with
    | false => exact (h ⟨x, hf⟩ rfl).elim
    | true => rfl
  · intro h y he
    subst x
    exact Bool.noConfusion (h.symm.trans y.2)

theorem size_cnf_le {n : ℕ} (f : BitString n → Bool) :
    size (cnf f) ≤ 2 ^ n + 1 := by
  classical
  have hc : Fintype.card {y : BitString n // f y = false} ≤ 2 ^ n := by
    simpa using Fintype.card_subtype_le (fun y : BitString n => f y = false)
  rw [cnf, size_gate]
  simp only [size_excludingClause, sum_const, card_univ, smul_eq_mul, mul_one]
  omega

/-- Every Boolean function has AND-rooted and OR-rooted depth-two layers. -/
theorem exists_depth_two {n : ℕ} (f : BitString n → Bool) (op : AndOrOp) :
    ∃ g : Layer n 2, size g ≤ 2 ^ n + 1 ∧ ∀ x, eval op g x = f x := by
  cases op with
  | and => exact ⟨cnf f, size_cnf_le f, eval_cnf f⟩
  | or =>
    refine ⟨neg (cnf (fun x => !(f x))), ?_, ?_⟩
    · simpa only [neg, size_mapInputs] using size_cnf_le (fun x => !(f x))
    · intro x
      exact (eval_neg _ .and x).trans (by simp [eval_cnf])

end Complexity.Shallow.Layer
