/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.RedBlack.Defs
public import Mathlib.Basic.Real.Basic
import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.RedBlack.Clusters.Internal
import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.RedBlack.Clusters.Internal.Partition
import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.RedBlack.Internal

/-!
# The bounded positive-set theorem from red density

First collect all original black components with at most `M` vertices.
A red edge within this union already gives a small positive witness.
Otherwise partition the remaining components into bounded connected sets
and apply the cluster incidence count. This supplies the red/black lemma
without a leaf reorganization or color-swap invariant.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Bisection.RedBlack.Internal

open scoped Classical

variable {V E : Type} [Fintype V] [Fintype E] (B : SimpleGraph V) (R : Multigraph V E)

theorem exists_positive_of_density (loopless : R.Loopless)
    (degree : ∀ v, B.degree v + R.degree v = 3) (M : ℕ) (positive : 0 < M)
    (density : (M + 4) * Fintype.card V < 2 * M * Fintype.card E) :
    ∃ X, X.card ≤ 3 * M * (1 + 3 * M) ∧ Positive B R X := by
  let U := Finset.univ.filter (fun v => Fintype.card (B.connectedComponentMk v) ≤ M)
  have small_iff (v : V) : v ∈ U ↔ Fintype.card (B.connectedComponentMk v) ≤ M := by
    simp only [U, Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases empty : internalEdges R U = ∅
  · have blackDegree (v : V) : B.degree v ≤ 3 := by have := degree v; lia
    obtain ⟨parts, cover, disjoint, pieces, count⟩ :=
      exists_large_component_partition B blackDegree M positive U small_iff
    exact exists_positive_of_partition B R loopless degree M (3 * M) U
      (fun v hv => (small_iff v).mp hv) empty parts disjoint cover
      (fun P hP => (pieces P hP).1) (fun P hP => (pieces P hP).2) count density
  · obtain ⟨e, he⟩ := Finset.nonempty_iff_ne_empty.mpr empty
    obtain ⟨first, second⟩ := (mem_internalEdges R).mp he
    obtain ⟨X, size, gain⟩ := exists_positive_of_component_edge B R
      (B.connectedComponentMk (R.fst e)) (B.connectedComponentMk (R.snd e)) M
      ((small_iff _).mp first) ((small_iff _).mp second) (by rfl) (by rfl)
    exact ⟨X, size.trans (by nlinarith), gain⟩

theorem exists_positive_of_red_density (loopless : R.Loopless)
    (degree : ∀ v, B.degree v + R.degree v = 3) (M : ℕ) (positive : 0 < M)
    {ε : ℝ} (budget : 2 ≤ ε * M)
    (density : (1 / 2 + ε) * Fintype.card V < Fintype.card E) :
    ∃ X, X.card ≤ 3 * M * (1 + 3 * M) ∧ Positive B R X := by
  apply exists_positive_of_density B R loopless degree M positive
  have mpos : (0 : ℝ) < M := by exact_mod_cast positive
  have scaled := mul_lt_mul_of_pos_left density (by positivity : (0 : ℝ) < 2 * M)
  have count := mul_le_mul_of_nonneg_right budget (Nat.cast_nonneg (α := ℝ) (Fintype.card V))
  have finite : ((M : ℝ) + 4) * Fintype.card V < 2 * M * Fintype.card E := by nlinarith
  exact_mod_cast finite

end Algebraic.Cutwidth.Bisection.RedBlack.Internal
