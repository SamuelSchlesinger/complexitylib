/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.SparseThresholds
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.SparseTree
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.SparseLeafCount
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.SparseLeafCNF
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Tactic.FieldSimp

/-!
# Unrestricted depth-three lower bound: sparse partition

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DepthThree/SparsePartition.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical proofs are retained.
-/

@[expose] public section

namespace Complexity

noncomputable section

namespace DepthThreeLowerBound

open scoped BigOperators

universe u

theorem sparse_entropy_sum_budget (b m : ℕ) (η : ℝ) (hb : 1 ≤ b) (hη : 0 < η)
    (r F : ℕ → ℕ) (hF0 : F 0 = 0) (hF1 : F 1 = 0)
    (hbound : ∀ i, 2 ≤ i → i ≤ b →
      (F i : ℝ) * binaryEntropy (1 / (r i : ℝ)) ≤ η / (b : ℝ)) :
    (∑ i : Fin (b + 1), ((F i.val * m : ℕ) : ℝ) *
      binaryEntropy (1 / (r i.val : ℝ))) ≤ η * (m : ℝ) := by
  have hbpos : (0 : ℝ) < b := by exact_mod_cast (show 0 < b by omega)
  have hδ : 0 ≤ η / (b : ℝ) := (div_pos hη hbpos).le
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, hF0, Nat.cast_zero, zero_mul, zero_add,
    Fin.val_succ]
  calc
    (∑ i : Fin b, ((F (i.val + 1) * m : ℕ) : ℝ) *
        binaryEntropy (1 / (r (i.val + 1) : ℝ))) ≤
        ∑ _i : Fin b, (m : ℝ) * (η / (b : ℝ)) := by
      apply Finset.sum_le_sum
      intro i _
      have hi : (F (i.val + 1) : ℝ) *
          binaryEntropy (1 / (r (i.val + 1) : ℝ)) ≤ η / (b : ℝ) := by
        by_cases hi1 : i.val + 1 = 1
        · simpa only [hi1, hF1, Nat.cast_zero, zero_mul] using hδ
        · exact hbound _ (by omega) (Nat.succ_le_of_lt i.isLt)
      simpa only [Nat.cast_mul, mul_assoc, mul_comm, mul_left_comm] using
        mul_le_mul_of_nonneg_left hi (Nat.cast_nonneg m)
    _ = η * (m : ℝ) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp [ne_of_gt hbpos]

/-- A finite partition into sparse CNF leaves with the required evaluation identity. -/
structure SparsePartition {V : Type u} [Fintype V]
    (H : CNF V) (b M : ℕ) (η : ℝ) where
  /-- Number of pieces in the sparse partition. -/
  count : ℕ
  /-- The sparse CNF at each partition index. -/
  piece : Fin count → CNF V
  normalized : ∀ i, (piece i).Normalized
  width_le : ∀ i, (piece i).WidthAtMost b
  clauses_le : ∀ i, (piece i).length ≤ M * Fintype.card V
  disjoint : ∀ i j, i ≠ j → ∀ x,
    ¬ ((piece i).eval x = true ∧ (piece j).eval x = true)
  indicator_eq_sum : ∀ x, indicator (H.eval x) =
    ∑ i, indicator ((piece i).eval x)
  count_le : (count : ℝ) ≤ (2 : ℝ) ^ (η * (Fintype.card V : ℝ))

theorem exists_sparse_partition_constant (b : ℕ) (η : ℝ)
    (hb : 1 ≤ b) (hη : 0 < η) :
    ∃ M : ℕ, 0 < M ∧
      ∀ (V : Type u) [Fintype V] [DecidableEq V] (H : CNF V),
        H.WidthAtMost b → Nonempty (SparsePartition H b M η) := by
  classical
  obtain ⟨r, e, D, F, M, hnum, hr, hF0, hF1, hFsum, hentropy, hM, hMpos⟩ :=
    exists_sparse_numerics b η hb hη
  refine ⟨M, hMpos, ?_⟩
  intro V _ _ H hwidth
  rcases exists_sparseNormalization_or_false H hwidth with hfalse | hA
  · refine ⟨{
      count := 0
      piece := fun i => Fin.elim0 i
      normalized := fun i => Fin.elim0 i
      width_le := fun i => Fin.elim0 i
      clauses_le := fun i => Fin.elim0 i
      disjoint := fun i => Fin.elim0 i
      indicator_eq_sum := ?_
      count_le := ?_
    }⟩
    · intro x
      simp [hfalse x]
    · simpa only [Nat.cast_zero] using
        (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (η * (Fintype.card V : ℝ)))
  · let A : SparseNormalization H b := Classical.choice hA
    let s := A.toState
    have hs : s.Valid b := A.toState_valid
    have hadded : s.added = ∅ := rfl
    let T := sparseTree r D b s hs
    let eqv := Fintype.equivFin T.tree.Leaf
    have hcount : (Fintype.card T.tree.Leaf : ℝ) ≤
        (2 : ℝ) ^ (η * (Fintype.card V : ℝ)) := by
      apply T.tree.card_le_of_entropy_budget
        (fun i => F i.val * Fintype.card V) (fun i => r i.val)
      · intro i
        exact hr i.val
      · intro p i
        rw [hFsum]
        exact sparseTree_stream_length hnum s hs hadded p i
      · intro p i
        rw [hFsum]
        exact sparseTree_stream_ones hnum s hs hadded p i
      · exact sparse_entropy_sum_budget b (Fintype.card V) η hb hη r F hF0 hF1 hentropy
    refine ⟨{
      count := Fintype.card T.tree.Leaf
      piece := fun i => (T.finish (eqv.symm i)).toCNF
      normalized := ?_
      width_le := ?_
      clauses_le := ?_
      disjoint := ?_
      indicator_eq_sum := ?_
      count_le := hcount
    }⟩
    · intro i
      exact (T.finish (eqv.symm i)).toCNF_normalized ((T.path (eqv.symm i)).valid hs)
    · intro i
      exact (T.finish (eqv.symm i)).toCNF_widthAtMost
        ((T.path (eqv.symm i)).valid hs) hb
    · intro i
      rw [hM]
      exact (T.finish (eqv.symm i)).toCNF_length_le_of_terminal
        ((T.path (eqv.symm i)).valid hs) hnum
        (sparseTree_terminal hnum s hs hadded (eqv.symm i))
    · intro i j hij x
      exact T.disjoint (eqv.symm i) (eqv.symm j)
        (fun h => hij (eqv.symm.injective h)) x
    · intro x
      change indicator (H.eval x) =
        ∑ i, indicator ((T.finish (eqv.symm i)).eval x)
      calc
        indicator (H.eval x) = indicator (s.eval x) :=
          congrArg indicator (A.toState_eval x).symm
        _ = ∑ p, indicator ((T.finish p).eval x) := T.indicator_eq_sum x
        _ = ∑ i, indicator ((T.finish (eqv.symm i)).eval x) := by
          simpa only [Equiv.symm_apply_apply] using
            eqv.sum_comp (fun i => indicator ((T.finish (eqv.symm i)).eval x))

end DepthThreeLowerBound

end

end Complexity
