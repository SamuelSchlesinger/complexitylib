/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Defs
public import Mathlib.Data.Fin.Tuple.Basic
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Probability

/-!
# Head and prefix weight identities

Separating the head from a finite tuple reindexes a sum bijectively.
A nonempty prefix fixes the head and then takes the corresponding prefix
of the unnormalized tail row. These identities hold for arbitrary weights.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

open scoped Classical

theorem block_sum_cons {α : Type*} [Fintype α] {t : Nat}
    (p : (Fin (t + 1) → α) → ℝ) :
    (∑ x, p x) = ∑ a, ∑ z : Fin t → α, p (Fin.cons a z) := by
  calc
    _ = ∑ az : α × (Fin t → α), p (Fin.cons az.1 az.2) :=
      ((Fin.consEquiv (fun _ : Fin (t + 1) => α)).sum_comp p).symm
    _ = _ := Fintype.sum_prod_type _

theorem blockPrefix_cons {α : Type*} {i t : Nat} (h : i ≤ t)
    (a : α) (z : Fin t → α) :
    blockPrefix (Nat.succ_le_succ h) (Fin.cons a z) = Fin.cons a (blockPrefix h z) := by
  funext j
  cases j using Fin.cases <;> simp [blockPrefix]

theorem blockPrefixWeight_cons {α : Type*} [Fintype α] {i t : Nat}
    (p : (Fin (t + 1) → α) → ℝ) (h : i ≤ t) (a : α) (u : Fin i → α) :
    blockPrefixWeight p (Nat.succ_le_succ h) (Fin.cons a u) =
      blockPrefixWeight (fun z : Fin t → α => p (Fin.cons a z)) h u := by
  unfold blockPrefixWeight mapWeight
  rw [block_sum_cons, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z _
  simp [blockPrefix_cons h, Fin.cons_inj, ite_and]

theorem blockPrefixWeight_scale {α : Type*} [Fintype α] {i t : Nat}
    (p : (Fin t → α) → ℝ) (c : ℝ) (h : i ≤ t) (u : Fin i → α) :
    blockPrefixWeight (fun x => c * p x) h u = c * blockPrefixWeight p h u := by
  unfold blockPrefixWeight mapWeight
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  by_cases same : blockPrefix h x = u <;> simp [same]

theorem mapWeight_blockHead_apply {α : Type*} [Fintype α] {t : Nat}
    (p : (Fin (t + 1) → α) → ℝ) (a : α) :
    mapWeight (fun x => x 0) p a = ∑ z : Fin t → α, p (Fin.cons a z) := by
  unfold mapWeight
  rw [block_sum_cons, Finset.sum_comm]
  simp

end Algebraic.Cutwidth.Extractor.Internal
