/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.SparsePartition
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.RestrictionCorrelation

/-!
# Unrestricted depth-three lower bound: sparse correlation

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DepthThree/SparseCorrelation.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical proofs are retained.
-/

@[expose] public section

namespace Complexity

noncomputable section

namespace DepthThreeLowerBound

open scoped BigOperators Classical

universe u

namespace SparsePartition

variable {V : Type u} [Fintype V]

theorem correlation_eq_sum {H : CNF V} {b M : ℕ} {η : ℝ}
    (P : SparsePartition H b M η) (G : Cube V → ℝ) :
    finiteAvg (fun x => G x * indicator (H.eval x)) =
      ∑ i, finiteAvg (fun x => G x * indicator ((P.piece i).eval x)) := by
  calc
    finiteAvg (fun x => G x * indicator (H.eval x)) =
        finiteAvg (fun x => ∑ i, G x * indicator ((P.piece i).eval x)) := by
      apply finiteAvg_congr
      intro x
      rw [P.indicator_eq_sum x, Finset.mul_sum]
    _ = _ := finiteAvg_sum Finset.univ
      (fun i x => G x * indicator ((P.piece i).eval x))

theorem abs_correlation_le {H : CNF V} {b M : ℕ} {η δ : ℝ}
    (P : SparsePartition H b M η) (G : Cube V → ℝ) (hδ : 0 ≤ δ)
    (hpiece : ∀ i, |finiteAvg (fun x => G x * indicator ((P.piece i).eval x))| ≤ δ) :
    |finiteAvg (fun x => G x * indicator (H.eval x))| ≤
      (2 : ℝ) ^ (η * (Fintype.card V : ℝ)) * δ := by
  rw [P.correlation_eq_sum G]
  calc
    |∑ i, finiteAvg (fun x => G x * indicator ((P.piece i).eval x))| ≤
        ∑ i, |finiteAvg (fun x => G x * indicator ((P.piece i).eval x))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin P.count, δ := Finset.sum_le_sum (fun i _ => hpiece i)
    _ = (P.count : ℝ) * δ := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right P.count_le hδ

end SparsePartition

theorem exists_sparse_correlation_transfer (b : ℕ) (η : ℝ)
    (hb : 1 ≤ b) (hη : 0 < η) :
    ∃ M : ℕ, 0 < M ∧
      ∀ (V : Type u) [Fintype V] [DecidableEq V] (G : Cube V → ℝ) (δ : ℝ),
        0 ≤ δ →
        (∀ H : CNF V, H.Normalized → H.WidthAtMost b →
          H.length ≤ M * Fintype.card V →
          |finiteAvg (fun x => G x * indicator (H.eval x))| ≤ δ) →
        corr b G ≤ (2 : ℝ) ^ (η * (Fintype.card V : ℝ)) * δ := by
  obtain ⟨M, hM, hpartition⟩ := exists_sparse_partition_constant b η hb hη
  refine ⟨M, hM, ?_⟩
  intro V _ _ G δ hδ htests
  apply corr_le_of_forall
  intro H hH
  obtain ⟨P⟩ := hpartition V H hH
  apply P.abs_correlation_le G hδ
  intro i
  exact Eq.mp
    (congrArg (fun inst : Fintype (Cube V) =>
      |@finiteAvg (Cube V) inst (fun x => G x * indicator ((P.piece i).eval x))| ≤ δ)
      (Subsingleton.elim _ _))
    (htests (P.piece i) (P.normalized i) (P.width_le i) (P.clauses_le i))

theorem exists_sparse_correlation_constant (b : ℕ) (hb : 1 ≤ b) :
    ∃ M : ℕ, 0 < M ∧
      ∀ (V : Type u) [Fintype V] [DecidableEq V] (G : Cube V → ℝ),
        (∀ H : CNF V, H.Normalized → H.WidthAtMost b →
          H.length ≤ M * Fintype.card V →
          |finiteAvg (fun x => G x * indicator (H.eval x))| ≤
            (2 : ℝ) ^ (-(Fintype.card V : ℝ) / 4)) →
        corr b G ≤ (2 : ℝ) ^ (-(Fintype.card V : ℝ) / 8) := by
  obtain ⟨M, hM, htransfer⟩ := exists_sparse_correlation_transfer b (1 / 8) hb (by norm_num)
  refine ⟨M, hM, ?_⟩
  intro V _ _ G htests
  have h := htransfer V G ((2 : ℝ) ^ (-(Fintype.card V : ℝ) / 4))
    (Real.rpow_nonneg (by norm_num) _) htests
  calc
    corr b G ≤ (2 : ℝ) ^ ((1 / 8) * (Fintype.card V : ℝ)) *
        (2 : ℝ) ^ (-(Fintype.card V : ℝ) / 4) := h
    _ = (2 : ℝ) ^ (-(Fintype.card V : ℝ) / 8) := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      congr 1
      ring

end DepthThreeLowerBound

end

end Complexity
