/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Mathlib.LinearAlgebra.Dimension.LinearMap
-- Required directly by CSLib's current Mathlib pin for the field rank-nullity instance.
public import Mathlib.LinearAlgebra.Dimension.DivisionRing -- shake: keep

/-!
# Rank bounds for finite spans of linear maps

Rank subadditivity bounds the rank of any linear combination by the sum of
rank budgets for its generators. No finite-dimensionality assumption is
needed: ranks are cardinals, while the supplied budgets are natural numbers.
-/

public section

namespace LinearMap

variable {K : Type u} {A : Type v} {B : Type w}
variable [Field K] [AddCommGroup A] [Module K A] [AddCommGroup B] [Module K B]

/-- Rank of a scalar multiple of a linear map is at most its rank. -/
theorem rank_smul_le
    (scalar : K)
    (map : A →ₗ[K] B) :
    LinearMap.rank (scalar • map) ≤ LinearMap.rank map :=
  Submodule.rank_mono (LinearMap.range_smul_le_range map scalar)

/-- The rank of a linear map in the span of a finite family is at most the
sum of any pointwise rank budgets for that family. -/
theorem rank_le_sum_of_mem_span
    {ι : Type z}
    [Fintype ι]
    (target : A →ₗ[K] B)
    (family : ι → A →ₗ[K] B)
    (budget : ι → Nat)
    (targetMem : target ∈ Submodule.span K (Set.range family))
    (localBound : ∀ index, LinearMap.rank (family index) ≤ budget index) :
    LinearMap.rank target ≤ ∑ index, (budget index : Cardinal) := by
  classical
  obtain ⟨coefficients, rfl⟩ :=
    (Submodule.mem_span_range_iff_exists_fun K).mp targetMem
  exact (LinearMap.rank_finsetSum_le Finset.univ
    (fun index => coefficients index • family index)).trans
    (Finset.sum_le_sum fun index _ =>
      (rank_smul_le (coefficients index) (family index)).trans (localBound index))

end LinearMap
