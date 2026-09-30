/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.SparseSynthesis.Internal.Matrix
public import Complexitylib.Circuits.SparseSynthesis.Internal.Intervals
public import Complexitylib.Circuits.SparseSynthesis.Internal.ExtensionBank

/-!
# Partial truth-table synthesis

Intervals containing few specified positions use a shared bank of total
extensions. Every extension is masked to its interval before the row is
assembled, so unconstrained values cannot affect another interval's data.
-/

@[expose] public section

namespace Complexity.CircuitSparseSynthesis.Internal

open Cslib Cslib.Circuits Cslib.Circuits.Boolean
open scoped BigOperators

/-- Shared minterms, interval-masked extension bank, and one OR per partial chunk. -/
def partialTableBudget (k l K weight : ℕ) : ℕ :=
  (2 ^ k + 2 ^ l) * (2 * (k + l) + 1) +
    (2 ^ k + 1) ^ 3 * (4 * 2 ^ k + 1) * 2 ^ K + weight / K + 4 * 2 ^ l + 1

theorem exists_partialTable {k l : ℕ} (domain : Finset (Fin (k + l) → Bool))
    (f : BooleanFunction (k + l)) (K : ℕ) (positive : 0 < K) :
    ∃ c : Circuit signature (k + l) 1,
      c.ComputesOn interpretation (domain : Set _) (fun x _ => f x) ∧
        c.size ≤ partialTableBudget k l K domain.card := by
  classical
  obtain ⟨extensions, bankSize, covers⟩ := exists_extension_bank (2 ^ k) K
  let B := Fin (2 ^ k + 1) × Fin (2 ^ k + 1) × extensions
  let patterns (b : B) (c : Fin (2 ^ k)) :=
    decide (b.1.val ≤ c.val ∧ c.val < b.2.1.val) && b.2.2.val c
  let count (r : Fin (2 ^ l)) := (rowDomain domain r).card / K + 1
  have extend (r : Fin (2 ^ l)) (b : Fin (count r)) :
      ∃ extension ∈ extensions, ∀ i ∈ intervalChunk (rowDomain domain r) K b.val,
        extension i = f (matrixInput r i) :=
    covers _ (intervalChunk_card _ _ _) (fun i => f (matrixInput r i))
  choose extension member correct using extend
  let chosen (r : Fin (2 ^ l)) (b : Fin (count r)) : B :=
    (supportCut (rowDomain domain r) (b.val * K),
      supportCut (rowDomain domain r) ((b.val + 1) * K), ⟨extension r b, member r b⟩)
  have small (b : B) :
      (Finset.univ.filter fun c => patterns b c = true).card ≤ 2 ^ k := by
    simpa using (Finset.univ.filter fun c => patterns b c = true).card_le_univ
  obtain ⟨c, hc, hsize⟩ := (matrix_synthesis patterns (2 ^ k) small count chosen).exists_circuit
  refine ⟨c, ?_, hsize.trans ?_⟩
  · intro x hx
    rw [hc x]
    funext j
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    have inRow : columnAt x ∈ rowDomain domain (rowAt x) := by simpa [rowDomain] using hx
    constructor
    · rintro ⟨b, hb⟩
      have split : (supportCut (rowDomain domain (rowAt x)) (b.val * K)).val ≤
          (columnAt x).val ∧ (columnAt x).val <
          (supportCut (rowDomain domain (rowAt x)) ((b.val + 1) * K)).val ∧
          extension (rowAt x) b (columnAt x) = true := by
        simpa [patterns, chosen, and_assoc] using hb
      have hchunk : columnAt x ∈ intervalChunk (rowDomain domain (rowAt x)) K b.val :=
        Finset.mem_filter.mpr ⟨inRow, split.1, split.2.1⟩
      simpa [correct (rowAt x) b (columnAt x) hchunk] using split.2.2
    · intro htrue
      obtain ⟨b, hb⟩ := exists_intervalChunk (rowDomain domain (rowAt x)) K positive
        (columnAt x) inRow
      refine ⟨b, ?_⟩
      have values := correct (rowAt x) b (columnAt x) hb
      have bounds := (Finset.mem_filter.mp hb).2
      simp [patterns, chosen, bounds, values, htrue]
  · have sumBound : ∑ r, count r ≤ domain.card / K + 2 ^ l := by
      simp only [count, Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul,
        Finset.card_univ, Fintype.card_fin, mul_one]
      exact Nat.add_le_add_right
        ((sum_div_le_div_sum Finset.univ (fun r => (rowDomain domain r).card) K).trans_eq
          (by rw [sum_rowDomain_card])) _
    have cost : Fintype.card B * (2 ^ k + 1) ≤
        (2 ^ k + 1) ^ 3 * (4 * 2 ^ k + 1) * 2 ^ K := by
      calc
        _ = (2 ^ k + 1) ^ 3 * extensions.card := by
          simp [B, Fintype.card_prod, Fintype.card_coe]; ring
        _ ≤ (2 ^ k + 1) ^ 3 * ((4 * 2 ^ k + 1) * 2 ^ K) :=
          Nat.mul_le_mul_left _ bankSize
        _ = _ := by ring
    unfold partialTableBudget
    omega

end Complexity.CircuitSparseSynthesis.Internal
