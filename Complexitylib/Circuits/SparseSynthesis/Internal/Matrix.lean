/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Cslib.Circuit.Boolean.Complexity
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic

/-!
# Shared pattern tables

A Boolean matrix is synthesized by sharing its column patterns across rows.
The leading cost is one OR per selected pattern; input tests and the pattern
bank are built only once. This is the elementary table construction used in
the sparse and partial-function specializations of local coding.
-/

@[expose] public section

namespace Complexity.CircuitSparseSynthesis.Internal

open Cslib Cslib.Circuits Cslib.Circuits.Boolean
open scoped BigOperators

/-- Binary numbering of all assignments to `width` input bits. -/
def assignmentIndex (width : ℕ) : (Fin width → Bool) ≃ Fin (2 ^ width) :=
  (Equiv.arrowCongr (Equiv.refl (Fin width)) finTwoEquiv.symm).trans finFunctionFinEquiv

/-- Column index selected by the first `k` input bits. -/
def columnAt {k l : ℕ} (x : Fin (k + l) → Bool) : Fin (2 ^ k) :=
  assignmentIndex k (fun i => x (Fin.castAdd l i))

/-- Row index selected by the remaining `l` input bits. -/
def rowAt {k l : ℕ} (x : Fin (k + l) → Bool) : Fin (2 ^ l) :=
  assignmentIndex l (fun i => x (Fin.natAdd k i))

/-- Reconstruct an input from its row and column indices. -/
def matrixInput {k l : ℕ} (row : Fin (2 ^ l)) (column : Fin (2 ^ k)) :
    Fin (k + l) → Bool :=
  Fin.append ((assignmentIndex k).symm column) ((assignmentIndex l).symm row)

@[simp] theorem columnAt_matrixInput {k l : ℕ} (r : Fin (2 ^ l)) (c : Fin (2 ^ k)) :
    columnAt (matrixInput r c) = c := by simp [columnAt, matrixInput]

@[simp] theorem rowAt_matrixInput {k l : ℕ} (r : Fin (2 ^ l)) (c : Fin (2 ^ k)) :
    rowAt (matrixInput r c) = r := by simp [rowAt, matrixInput]

@[simp] theorem matrixInput_rowAt_columnAt {k l : ℕ} (x : Fin (k + l) → Bool) :
    matrixInput (rowAt x) (columnAt x) = x := by
  simp [matrixInput, rowAt, columnAt, Fin.append_castAdd_natAdd]

/-- The truth-table indexing equivalence used to sum support sizes over rows. -/
def matrixEquiv (k l : ℕ) : (Fin (k + l) → Bool) ≃ Fin (2 ^ l) × Fin (2 ^ k) where
  toFun x := (rowAt x, columnAt x)
  invFun rc := matrixInput rc.1 rc.2
  left_inv := matrixInput_rowAt_columnAt
  right_inv rc := by simp

/-- Columns of one row whose corresponding inputs belong to the domain. -/
def rowDomain {k l : ℕ} (domain : Finset (Fin (k + l) → Bool)) (r : Fin (2 ^ l)) :
    Finset (Fin (2 ^ k)) :=
  Finset.univ.filter fun c => matrixInput r c ∈ domain

theorem sum_rowDomain_card {k l : ℕ} (domain : Finset (Fin (k + l) → Bool)) :
    ∑ r, (rowDomain domain r).card = domain.card := by
  classical
  have h := Fintype.sum_equiv (matrixEquiv k l)
    (fun x => if x ∈ domain then (1 : ℕ) else 0)
    (fun rc => if matrixInput rc.1 rc.2 ∈ domain then 1 else 0)
    (fun x => by simp [matrixEquiv])
  calc
    _ = ∑ rc : Fin (2 ^ l) × Fin (2 ^ k),
        if matrixInput rc.1 rc.2 ∈ domain then (1 : ℕ) else 0 := by
      simp only [rowDomain, Finset.card_eq_sum_ones, Finset.sum_filter,
        Fintype.sum_prod_type]
    _ = ∑ x, if x ∈ domain then (1 : ℕ) else 0 := h.symm
    _ = domain.card := by simp

/-- Shared equality tests for every column and row index. -/
def matrixMinterm {k l : ℕ} : Fin (2 ^ k) ⊕ Fin (2 ^ l) → BooleanFunction (k + l)
  | .inl c => fun x => decide (columnAt x = c)
  | .inr r => fun x => decide (rowAt x = r)

theorem matrixMinterms_synthesis (k l : ℕ) :
    Synthesis interpretation (inputs (k + l)) (Set.range (matrixMinterm (k := k) (l := l)))
      ((2 ^ k + 2 ^ l) * (2 * (k + l) + 1)) := by
  have each (i : Fin (2 ^ k) ⊕ Fin (2 ^ l)) :
      Synthesis interpretation (inputs (k + l)) {matrixMinterm i}
        (2 * (k + l) + 1) := by
    cases i with
    | inl c =>
        have eqn : matrixMinterm (l := l) (.inl c) =
            (fun x => decide ((fun i => x (Fin.castAdd l i)) =
              (assignmentIndex k).symm c)) := by
          funext x
          apply Bool.eq_iff_iff.mpr
          simp only [matrixMinterm, decide_eq_true_eq]
          exact (assignmentIndex k).eq_symm_apply.symm
        rw [eqn]
        exact (synthesis_minterm (Fin.castAdd l) _).mono
          Set.Subset.rfl Set.Subset.rfl (by omega)
    | inr r =>
        have eqn : matrixMinterm (k := k) (.inr r) =
            (fun x => decide ((fun i => x (Fin.natAdd k i)) =
              (assignmentIndex l).symm r)) := by
          funext x
          apply Bool.eq_iff_iff.mpr
          simp only [matrixMinterm, decide_eq_true_eq]
          exact (assignmentIndex l).eq_symm_apply.symm
        rw [eqn]
        exact (synthesis_minterm (Fin.natAdd k) _).mono
          Set.Subset.rfl Set.Subset.rfl (by omega)
  simpa using Synthesis.family _ (fun _ => 2 * (k + l) + 1) each

theorem pattern_synthesis {k l : ℕ} (pattern : Fin (2 ^ k) → Bool) :
    Synthesis interpretation (Set.range (matrixMinterm (k := k) (l := l)))
      {fun x => pattern (columnAt x)}
      ((Finset.univ.filter fun c => pattern c = true).card + 1) := by
  have h := Synthesis.exists_mem (Finset.univ.filter fun c => pattern c = true)
    (fun c => matrixMinterm (l := l) (.inl c)) (fun _ => 0)
    (fun c _ => Synthesis.of_mem
      (s := Set.range (matrixMinterm (k := k) (l := l))) ⟨.inl c, rfl⟩)
  apply h.mono Set.Subset.rfl ?_ (by simp)
  rintro q rfl
  simp only [Set.mem_singleton_iff]
  funext x
  apply Bool.eq_iff_iff.mpr
  simp [matrixMinterm]

theorem matrix_synthesis {k l : ℕ} {B : Type} [Fintype B]
    (patterns : B → Fin (2 ^ k) → Bool) (patternSize : ℕ)
    (small : ∀ b, (Finset.univ.filter fun c => patterns b c = true).card ≤ patternSize)
    (count : Fin (2 ^ l) → ℕ) (chosen : ∀ row, Fin (count row) → B) :
    Synthesis interpretation (inputs (k + l))
      {fun x => decide (∃ j, patterns (chosen (rowAt x) j) (columnAt x) = true)}
      ((2 ^ k + 2 ^ l) * (2 * (k + l) + 1) + Fintype.card B * (patternSize + 1) +
        (∑ row, count row) + 3 * 2 ^ l + 1) := by
  classical
  let bank (b : B) : BooleanFunction (k + l) := fun x => patterns b (columnAt x)
  let rowValue (r : Fin (2 ^ l)) : BooleanFunction (k + l) :=
    fun x => decide (∃ j, patterns (chosen r j) (columnAt x) = true)
  have hbank : Synthesis interpretation (Set.range matrixMinterm) (Set.range bank)
      (Fintype.card B * (patternSize + 1)) := by
    simpa using Synthesis.family bank (fun _ => patternSize + 1) (fun b =>
      (pattern_synthesis (l := l) (patterns b)).mono
        Set.Subset.rfl Set.Subset.rfl (Nat.add_le_add_right (small b) 1))
  have hrow (r : Fin (2 ^ l)) :
      Synthesis interpretation (Set.range matrixMinterm ∪ Set.range bank)
        {fun x => matrixMinterm (.inr r) x && rowValue r x} (count r + 2) := by
    have h := Synthesis.exists_mem Finset.univ (fun j => bank (chosen r j))
      (fun _ => 0) (fun j _ => Synthesis.of_mem
        (s := Set.range (matrixMinterm (k := k) (l := l)) ∪ Set.range bank)
        (Or.inr ⟨chosen r j, rfl⟩))
    have h' : Synthesis interpretation (Set.range matrixMinterm ∪ Set.range bank)
        {rowValue r} (count r + 1) := by simpa [rowValue, bank] using h
    simpa only [zero_add, Nat.add_assoc, Nat.reduceAdd] using
      (Synthesis.of_mem (Or.inl ⟨Sum.inr r, rfl⟩)).and h'
  have hrows := Synthesis.exists_mem Finset.univ
    (fun r x => matrixMinterm (.inr r) x && rowValue r x)
    (fun r => count r + 2) (fun r _ => hrow r)
  have hrows' : Synthesis interpretation (Set.range matrixMinterm ∪ Set.range bank)
      {fun x => decide (∃ j, patterns (chosen (rowAt x) j) (columnAt x) = true)}
      ((∑ row, count row) + 3 * 2 ^ l + 1) := by
    apply hrows.mono Set.Subset.rfl ?_ (by
      simp [Nat.add_assoc, Finset.sum_add_distrib, Nat.mul_comm])
    rintro q rfl
    simp only [Set.mem_singleton_iff]
    funext x
    apply Bool.eq_iff_iff.mpr
    simp [matrixMinterm, rowValue]
  have all := (matrixMinterms_synthesis k l).comp
    (hbank.mono Set.subset_union_right Set.Subset.rfl le_rfl)
  have final := all.trans (hrows'.mono Set.subset_union_right Set.Subset.rfl le_rfl)
  simpa only [Nat.add_assoc] using final

end Complexity.CircuitSparseSynthesis.Internal
