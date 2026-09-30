/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Finset.Option
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-!
# Finite chunks of a support

Enumerating a finite support in chunks gives at most `card / size + 1`
patterns, each containing at most `size` positions.
-/

@[expose] public section

namespace Complexity.CircuitSparseSynthesis.Internal

open scoped BigOperators

variable {α : Type} [DecidableEq α]

/-- The positions named by a tuple, ignoring empty entries and repetitions. -/
def tupleSupport {K : ℕ} (v : Fin K → Option α) : Finset α :=
  Finset.univ.biUnion fun i => (v i).toFinset

@[simp] theorem mem_tupleSupport {K : ℕ} (v : Fin K → Option α) (a : α) :
    a ∈ tupleSupport v ↔ ∃ i, v i = some a := by
  simp [tupleSupport]

theorem tupleSupport_card {K : ℕ} (v : Fin K → Option α) : (tupleSupport v).card ≤ K := by
  calc
    _ ≤ ∑ i : Fin K, ((v i).toFinset.card) := Finset.card_biUnion_le
    _ ≤ ∑ _i : Fin K, 1 := Finset.sum_le_sum fun i _ => by cases v i <;> simp
    _ = K := by simp

/-- One chunk of an enumeration of `s`, padded with empty entries. -/
noncomputable def chunkTuple (s : Finset α) (K block : ℕ) : Fin K → Option α :=
  fun i => if h : block * K + i.val < s.card then
    some (s.equivFin.symm ⟨block * K + i.val, h⟩).val else none

theorem mem_chunkTuple_iff (s : Finset α) (K : ℕ) (positive : 0 < K) (a : α) :
    (∃ block : Fin (s.card / K + 1), a ∈ tupleSupport (chunkTuple s K block.val)) ↔
      a ∈ s := by
  simp only [mem_tupleSupport]
  constructor
  · rintro ⟨block, i, hi⟩
    unfold chunkTuple at hi
    split at hi
    · have eqn := Option.some.inj hi
      exact eqn ▸ (s.equivFin.symm _).property
    · simp at hi
  · intro ha
    let rank := s.equivFin ⟨a, ha⟩
    let block : Fin (s.card / K + 1) :=
      ⟨rank.val / K, Nat.lt_succ_of_le (Nat.div_le_div_right rank.isLt.le)⟩
    let offset : Fin K := ⟨rank.val % K, Nat.mod_lt _ positive⟩
    have eqn : block.val * K + offset.val = rank.val := Nat.div_add_mod' _ _
    have valid : block.val * K + offset.val < s.card := eqn ▸ rank.isLt
    refine ⟨block, offset, ?_⟩
    simp only [chunkTuple, valid, dite_true, Option.some.injEq]
    have index : (⟨block.val * K + offset.val, valid⟩ : Fin s.card) = rank := Fin.ext eqn
    rw [index]
    exact congrArg Subtype.val (s.equivFin.symm_apply_apply ⟨a, ha⟩)

theorem sum_div_le_div_sum {ι : Type} (s : Finset ι) (f : ι → ℕ) (K : ℕ) :
    ∑ i ∈ s, f i / K ≤ (∑ i ∈ s, f i) / K := by
  by_cases positive : 0 < K
  · apply (Nat.le_div_iff_mul_le positive).mpr
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum fun i _ => Nat.div_mul_le_self _ _
  · have : K = 0 := by omega
    simp [this]

end Complexity.CircuitSparseSynthesis.Internal
