/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.DescriptiveComplexity.Circuit.Defs

/-!
# Correctness and bounds for finite quantifier expansion

Atomic selectors read the represented structure. The formula induction expands
finite quantification and gives exact polynomial tree size and constant depth.
-/

public section

namespace Complexity.DescriptiveComplexity.StructureInput

variable {V : Vocabulary} {card N n : Nat}

theorem termTest_true (A : DecFinStruct V) (L : StructureInput V A.card N)
    (input : BitString N) (h : Represents A L input) (σ : Env A.card n)
    (t : Term V n) (a : Fin A.card) :
    (L.termTest σ t a).eval input = true ↔ t.eval A.toFinStruct σ = a := by
  cases t <;> simp [termTest, AC0Formula.eval, Literal.eval, h.2, Term.eval,
    DecFinStruct.toFinStruct]

theorem relationTest_true (A : DecFinStruct V) (L : StructureInput V A.card N)
    (input : BitString N) (h : Represents A L input) (σ : Env A.card n)
    (i : Fin V.numRels) (ts : Fin (V.relArity i) → Term V n) :
    (L.relationTest σ i ts).eval input = true ↔
      A.rel i (fun j => (ts j).eval A.toFinStruct σ) = true := by
  simp only [relationTest, AC0Formula.eval_orList, List.any_map, List.any_eq_true,
    Function.comp_apply, AC0Formula.eval_andList, List.all_cons, Bool.and_eq_true,
    AC0Formula.eval, Literal.eval, ite_true, h.1, List.all_map, List.all_eq_true,
    List.mem_finRange, forall_true_left, termTest_true A L input h]
  constructor
  · rintro ⟨args, _, ha, ht⟩
    exact (congrArg (A.rel i) (funext ht)).trans ha
  · intro ha
    exact ⟨_, mem_allTuples _ _ _, ha, fun _ => rfl⟩

theorem equalityTest_true (A : DecFinStruct V) (L : StructureInput V A.card N)
    (input : BitString N) (h : Represents A L input) (σ : Env A.card n)
    (t₁ t₂ : Term V n) :
    (L.equalityTest σ t₁ t₂).eval input = true ↔
      t₁.eval A.toFinStruct σ = t₂.eval A.toFinStruct σ := by
  simp only [equalityTest, AC0Formula.eval_orList, List.any_map, List.any_eq_true,
    Function.comp_apply, AC0Formula.eval_andList, List.all_cons, List.all_nil,
    Bool.and_eq_true, and_true, termTest_true A L input h, List.mem_finRange,
    true_and]
  exact ⟨fun ⟨_, h₁, h₂⟩ => h₁.trans h₂.symm, fun h => ⟨_, rfl, h.symm⟩⟩

theorem compile_sat_internal (A : DecFinStruct V) (L : StructureInput V A.card N)
    (input : BitString N) (h : Represents A L input) (φ : Formula V n) (σ : Env A.card n) :
    (L.compile φ σ).eval input = true ↔ φ.Sat A.toFinStruct σ := by
  induction φ with
  | relApp i ts => exact relationTest_true A L input h σ i ts
  | eq t₁ t₂ => exact equalityTest_true A L input h σ t₁ t₂
  | neg φ ih =>
    simp only [compile, AC0Formula.eval_neg, Bool.not_eq_true', Formula.Sat,
      ← ih σ, Bool.not_eq_true]
  | conj φ ψ ihφ ihψ =>
    simp [compile, AC0Formula.eval_andList, Formula.Sat, ihφ, ihψ]
  | disj φ ψ ihφ ihψ =>
    simp [compile, AC0Formula.eval_orList, Formula.Sat, ihφ, ihψ]
  | exist φ ih =>
    simp [compile, AC0Formula.eval_orList, Function.comp_def, Formula.Sat, ih]
    rfl
  | all φ ih =>
    simp [compile, AC0Formula.eval_andList, Function.comp_def, Formula.Sat, ih]
    rfl

theorem termTest_size (L : StructureInput V card N) (σ : Env card n)
    (t : Term V n) (a : Fin card) : (L.termTest σ t a).size = 1 := by
  cases t <;> rfl

theorem termTest_depth (L : StructureInput V card N) (σ : Env card n)
    (t : Term V n) (a : Fin card) : (L.termTest σ t a).depth = 0 := by
  cases t <;> rfl

theorem relationTest_size (L : StructureInput V card N) (σ : Env card n)
    (i : Fin V.numRels) (ts : Fin (V.relArity i) → Term V n) :
    (L.relationTest σ i ts).size = 1 + card ^ V.relArity i * (V.relArity i + 2) := by
  simp [relationTest, AC0Formula.size_orList, AC0Formula.size_andList, List.map_map,
    Function.comp_def, AC0Formula.size, termTest_size, allTuples_length, Nat.add_comm]
  omega

theorem equalityTest_size (L : StructureInput V card N) (σ : Env card n)
    (t₁ t₂ : Term V n) : (L.equalityTest σ t₁ t₂).size = 1 + card * 3 := by
  simp [equalityTest, AC0Formula.size_orList, AC0Formula.size_andList, List.map_map,
    Function.comp_def, termTest_size]

theorem compile_size_internal (L : StructureInput V card N) (φ : Formula V n)
    (σ : Env card n) : (L.compile φ σ).size = φ.expansionPolynomial.eval card := by
  induction φ <;> simp [compile, relationTest_size, equalityTest_size,
    Formula.expansionPolynomial, AC0Formula.size_neg, AC0Formula.size_andList,
    AC0Formula.size_orList, List.map_map, Function.comp_def, Nat.add_assoc, *]

theorem relationTest_depth_le (L : StructureInput V card N) (σ : Env card n)
    (i : Fin V.numRels) (ts : Fin (V.relArity i) → Term V n) :
    (L.relationTest σ i ts).depth ≤ 2 := by
  apply AC0Formula.depth_orList_le _ 1
  intro f hf
  obtain ⟨args, _, rfl⟩ := List.mem_map.mp hf
  apply AC0Formula.depth_andList_le _ 0
  intro g hg
  rcases List.mem_cons.mp hg with rfl | hg
  · exact Nat.le_refl 0
  · obtain ⟨j, _, rfl⟩ := List.mem_map.mp hg
    simp [termTest_depth]

theorem equalityTest_depth_le (L : StructureInput V card N) (σ : Env card n)
    (t₁ t₂ : Term V n) : (L.equalityTest σ t₁ t₂).depth ≤ 2 := by
  apply AC0Formula.depth_orList_le _ 1
  intro f hf
  obtain ⟨a, _, rfl⟩ := List.mem_map.mp hf
  apply AC0Formula.depth_andList_le _ 0
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl <;> simp [termTest_depth]

theorem compile_depth_internal (L : StructureInput V card N) (φ : Formula V n)
    (σ : Env card n) : (L.compile φ σ).depth ≤ φ.size + 1 := by
  induction φ with
  | relApp i ts => exact relationTest_depth_le L σ i ts
  | eq t₁ t₂ => exact equalityTest_depth_le L σ t₁ t₂
  | neg φ ih =>
    simpa only [compile, AC0Formula.depth_neg, Formula.size] using
      (ih σ).trans (Nat.le_succ _)
  | conj φ ψ ihφ ihψ =>
    apply AC0Formula.depth_andList_le _ (φ.size + ψ.size + 1)
    intro f hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl
    · exact (ihφ σ).trans (by omega)
    · exact (ihψ σ).trans (by omega)
  | disj φ ψ ihφ ihψ =>
    apply AC0Formula.depth_orList_le _ (φ.size + ψ.size + 1)
    intro f hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl
    · exact (ihφ σ).trans (by omega)
    · exact (ihψ σ).trans (by omega)
  | exist φ ih =>
    apply AC0Formula.depth_orList_le _ (φ.size + 1)
    intro f hf
    obtain ⟨a, _, rfl⟩ := List.mem_map.mp hf
    exact ih (envCons a σ)
  | all φ ih =>
    apply AC0Formula.depth_andList_le _ (φ.size + 1)
    intro f hf
    obtain ⟨a, _, rfl⟩ := List.mem_map.mp hf
    exact ih (envCons a σ)

end Complexity.DescriptiveComplexity.StructureInput
