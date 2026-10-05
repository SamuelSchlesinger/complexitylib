/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.MultiOutput.Linear.Rank
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Gaussian
import Complexitylib.Algebraic.LowerBound.Cutwidth.MultiOutput.TotallyRegular.Internal

/-!
# Totally regular linear realizations over arbitrary fields

A local linear realization on the original circuit wires supplies the rank bound
at every cut. The graph layout then gives the same gate lower bound over finite
and infinite fields. There is no restriction on the coefficients of the local
linear combinations, and no extra gate is charged for forming the certificate.
-/

@[expose] public section

namespace Algebraic.Cutwidth.MultiOutput.Linear

open Filter

/-- The finite layout bound for a local linear realization of a totally regular map. -/
theorem Realization.sub_one_le_of_totallyRegular {σ : Signature} {F : Type*} [Field F]
    {A η C : ℝ} (hAη : 0 ≤ A + η) (order : Multigraph.OrderingBound A η C)
    {n s : ℕ} {p : Program σ n s} (r : Realization p F) (fan : p.FanInAtMost 2)
    (out : Fin n → Wire n s) {M : Matrix (Fin n) (Fin n) F}
    (regular : TotallyRegular M) (rows : ∀ i, r.value (out i) = M i) :
    (n : ℝ) - 1 ≤ (A + η) * max ((s : ℝ) - n) 0 +
      3 * Real.logb 2 (n + 3 * s) + C :=
  Internal.sub_one_le_of_rank_cuts hAη order p fan out regular
    (r.outputs_injective out regular rows) (r.blockRank_add_blockRank_le out M rows)

universe u v

/-- The asymptotic transfer is uniform over fields, signatures, and local coefficients. -/
theorem eventually_lt_size_of_orderingBound {A : ℝ} (hA : 0 < A)
    (order : ∀ η : ℝ, 0 < η → ∃ C : ℝ, Multigraph.OrderingBound A η C)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ (F : Type u) [Field F] (M : Matrix (Fin n) (Fin n) F),
      TotallyRegular M → ∀ (σ : Signature.{v}) (c : Circuit σ n n),
        c.FanInAtMost 2 → ∀ r : Realization c.program F,
        (∀ i, r.value (c.outputs i) = M i) → (1 + 1 / A - ε) * n < c.size := by
  filter_upwards [Internal.eventually_lt_size_of_rank_cuts.{u, v} hA order hε]
    with n bound
  intro F _ M regular σ c fan r rows
  exact bound F M regular σ c fan (r.outputs_injective c.outputs regular rows)
    (r.blockRank_add_blockRank_le c.outputs M rows)

/-- The Gaussian coefficient for totally regular linear realizations over any field. -/
theorem eventually_lt_size_gaussian {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ (F : Type u) [Field F] (M : Matrix (Fin n) (Fin n) F),
      TotallyRegular M → ∀ (σ : Signature.{v}) (c : Circuit σ n n),
        c.FanInAtMost 2 → ∀ r : Realization c.program F,
        (∀ i, r.value (c.outputs i) = M i) →
        (1 + Real.pi / (3 * Real.arccos ((1 + 2 * Real.sqrt 2) / 4)) - ε) * n <
          c.size := by
  have bound := eventually_lt_size_of_orderingBound.{u, v}
    (mul_pos two_pos Gaussian.frontierCoefficient_pos)
    Multigraph.exists_orderingBound_frontier hε
  rwa [Gaussian.one_add_inv_two_mul_frontierCoefficient] at bound

end Algebraic.Cutwidth.MultiOutput.Linear
