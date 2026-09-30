/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.SparseSynthesis.Internal.Matrix
public import Complexitylib.Circuits.SparseSynthesis.Internal.Chunks

/-!
# Sparse truth-table synthesis

Each row is divided into short tuples of true columns. All possible tuples
are implemented once. The leading assembly cost is `weight / chunkSize`.
-/

@[expose] public section

namespace Complexity.CircuitSparseSynthesis.Internal

open Cslib Cslib.Circuits Cslib.Circuits.Boolean
open scoped BigOperators

/-- Shared minterms, all `K`-tuples of columns, and one OR per selected sparse chunk. -/
def sparseTableBudget (k l K weight : ℕ) : ℕ :=
  (2 ^ k + 2 ^ l) * (2 * (k + l) + 1) + (2 ^ k + 1) ^ K * (K + 1) +
    weight / K + 4 * 2 ^ l + 1

theorem sparseTable_synthesis {k l : ℕ} (domain : Finset (Fin (k + l) → Bool))
    (K : ℕ) (positive : 0 < K) :
    Synthesis interpretation (inputs (k + l)) {fun x => decide (x ∈ domain)}
      (sparseTableBudget k l K domain.card) := by
  classical
  let patterns (v : Fin K → Option (Fin (2 ^ k))) (c : Fin (2 ^ k)) : Bool :=
    decide (c ∈ tupleSupport v)
  let count (r : Fin (2 ^ l)) := (rowDomain domain r).card / K + 1
  let chosen (r : Fin (2 ^ l)) (b : Fin (count r)) :=
    chunkTuple (rowDomain domain r) K b.val
  have small (v : Fin K → Option (Fin (2 ^ k))) :
      (Finset.univ.filter fun c => patterns v c = true).card ≤ K := by
    simpa only [patterns, decide_eq_true_eq, Finset.filter_mem_eq_inter,
      Finset.univ_inter] using tupleSupport_card v
  have h := matrix_synthesis patterns K small count chosen
  apply h.mono Set.Subset.rfl ?_ ?_
  · rintro q rfl
    simp only [Set.mem_singleton_iff]
    funext x
    apply Bool.eq_iff_iff.mpr
    simp only [patterns, chosen, decide_eq_true_eq]
    rw [mem_chunkTuple_iff _ _ positive]
    simp [rowDomain]
  · have sumBound : ∑ r, count r ≤ domain.card / K + 2 ^ l := by
      simp only [count, Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul,
        Finset.card_univ, Fintype.card_fin, mul_one]
      exact Nat.add_le_add_right
        ((sum_div_le_div_sum Finset.univ (fun r => (rowDomain domain r).card) K).trans_eq
          (by rw [sum_rowDomain_card])) _
    simp only [Fintype.card_fun, Fintype.card_option, Fintype.card_fin]
    unfold sparseTableBudget
    omega

theorem exists_sparseTable {k l : ℕ} (domain : Finset (Fin (k + l) → Bool))
    (K : ℕ) (positive : 0 < K) :
    ∃ c : Circuit signature (k + l) 1,
      c.Computes interpretation (fun x _ => decide (x ∈ domain)) ∧
        c.size ≤ sparseTableBudget k l K domain.card :=
  (sparseTable_synthesis domain K positive).exists_circuit

end Complexity.CircuitSparseSynthesis.Internal
