/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.MultiOutput.Polynomial.Linearization
public import Complexitylib.Algebraic.LowerBound.Cutwidth.MultiOutput.Linear
public import Complexitylib.Algebraic.LowerBound.Cutwidth.MultiOutput.TotallyRegular
import Complexitylib.Algebraic.LowerBound.Cutwidth.MultiOutput.Rank
import Complexitylib.Algebraic.LowerBound.Cutwidth.MultiOutput.TotallyRegular.Internal

/-!
# Polynomial gates computing totally regular linear maps

Every fan-in-two circuit of polynomial gates computing a totally regular linear
map requires more than `(L-ε)n` gates eventually, with `L ≈ 4.5625`. Degrees,
coefficients, depth, and fanout are unrestricted. The threshold is uniform over
fields, matrices, signatures, and gate polynomials.

Over infinite fields, formal differentiation at zero supplies a local linear
realization on the original wires. Over finite fields, the earlier cardinality
argument supplies the same cut-rank bound, even for arbitrary gate functions.
The common graph-layout theorem then applies without changing the gate count.
Coefficients are part of a polynomial gate and incur no separate cost. Explicit
nullary gate occurrences are included in `Circuit.size`.

The totally-regular-map method is due to Valiant; the classical indegree-two
superconcentrator bound of Lev and Valiant gives coefficient four. This transfer
uses the library's stronger Gaussian ordering theorem. No historical-priority
claim for the resulting arithmetic coefficient is made here.
-/

@[expose] public section

namespace Algebraic.Cutwidth.MultiOutput.Polynomial

open Filter SingleCut Matrix

variable {σ : Signature} {F : Type*} [Field F]

/-- Polynomial circuits obey the rank bound at every wire cut over any field. -/
theorem blockRank_add_blockRank_le {I : Interpretation σ F} (polynomial : IsPolynomial I)
    {n m : ℕ} (c : Circuit σ n m) {M : Matrix (Fin m) (Fin n) F}
    (computes : c.Computes I (fun x => M *ᵥ x)) (S : Finset (Wire n c.size)) :
    blockRank M (outputsIn c.outputs S)ᶜ (inputsIn S) +
      blockRank M (outputsIn c.outputs S) (inputsIn S)ᶜ ≤
        (forward c.program S).card + (backward c.program S).card := by
  classical
  rcases finite_or_infinite F with finite | infinite
  · let : Finite F := finite
    let : Fintype F := Fintype.ofFinite F
    exact MultiOutput.blockRank_add_blockRank_le computes S
  · let : Infinite F := infinite
    exact (realization polynomial c.program).blockRank_add_blockRank_le c.outputs M
      (realization_output polynomial c M computes) S

/-- The finite polynomial-gate lower bound, with the original circuit's gate count. -/
theorem sub_one_le_of_totallyRegular {A η C : ℝ} (hAη : 0 ≤ A + η)
    (order : Multigraph.OrderingBound A η C) {I : Interpretation σ F}
    (polynomial : IsPolynomial I) {n : ℕ} (c : Circuit σ n n)
    (fan : c.FanInAtMost 2) {M : Matrix (Fin n) (Fin n) F}
    (regular : TotallyRegular M) (computes : c.Computes I (fun x => M *ᵥ x)) :
    (n : ℝ) - 1 ≤ (A + η) * max ((c.size : ℝ) - n) 0 +
      3 * Real.logb 2 (n + 3 * c.size) + C := by
  apply MultiOutput.Internal.sub_one_le_of_rank_cuts hAη order c.program fan c.outputs regular
  · refine MultiOutput.Internal.outputs_injective regular c.program I c.outputs
      (fun x i => congrFun (computes x) i) fun i i' equal j => ?_
    simpa [Matrix.mulVec_single_one] using equal (Pi.single j 1)
  · exact blockRank_add_blockRank_le polynomial c computes

universe u v

/-- Any ordering coefficient transfers uniformly to polynomial circuits over all fields. -/
theorem eventually_lt_size_of_totallyRegular_of_orderingBound {A : ℝ} (hA : 0 < A)
    (order : ∀ η : ℝ, 0 < η → ∃ C : ℝ, Multigraph.OrderingBound A η C)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ (F : Type u) [Field F] (M : Matrix (Fin n) (Fin n) F),
      TotallyRegular M → ∀ (σ : Signature.{v}) (I : Interpretation σ F),
        IsPolynomial I → ∀ c : Circuit σ n n, c.FanInAtMost 2 →
        c.Computes I (fun x => M *ᵥ x) → (1 + 1 / A - ε) * n < c.size := by
  filter_upwards [MultiOutput.Internal.eventually_lt_size_of_rank_cuts.{u, v} hA order hε]
    with n bound
  intro F _ M regular σ I polynomial c fan computes
  apply bound F M regular σ c fan
  · refine MultiOutput.Internal.outputs_injective regular c.program I c.outputs
      (fun x i => congrFun (computes x) i) fun i i' equal j => ?_
    simpa [Matrix.mulVec_single_one] using equal (Pi.single j 1)
  · exact blockRank_add_blockRank_le polynomial c computes

/-- Totally regular linear maps need `(4.5625…-ε)n` polynomial gates of fan-in at most two. -/
theorem eventually_lt_size_of_totallyRegular {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ (F : Type u) [Field F] (M : Matrix (Fin n) (Fin n) F),
      TotallyRegular M → ∀ (σ : Signature.{v}) (I : Interpretation σ F),
        IsPolynomial I → ∀ c : Circuit σ n n, c.FanInAtMost 2 →
        c.Computes I (fun x => M *ᵥ x) →
        (1 + Real.pi / (3 * Real.arccos ((1 + 2 * Real.sqrt 2) / 4)) - ε) * n <
          c.size := by
  have bound := eventually_lt_size_of_totallyRegular_of_orderingBound.{u, v}
    (mul_pos two_pos Gaussian.frontierCoefficient_pos)
    Multigraph.exists_orderingBound_frontier hε
  rwa [Gaussian.one_add_inv_two_mul_frontierCoefficient] at bound

/-- The full polynomial signature allows arbitrary coefficients and polynomial degrees. -/
theorem eventually_lt_size {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ (F : Type u) [Field F] (M : Matrix (Fin n) (Fin n) F),
      TotallyRegular M → ∀ c : Circuit (signature F) n n, c.FanInAtMost 2 →
        c.Computes (interpretation F) (fun x => M *ᵥ x) →
        (1 + Real.pi / (3 * Real.arccos ((1 + 2 * Real.sqrt 2) / 4)) - ε) * n <
          c.size := by
  filter_upwards [eventually_lt_size_of_totallyRegular.{u, u} hε] with n bound
  intro F _ M regular c fan computes
  exact bound F M regular (signature F) (interpretation F) isPolynomial_interpretation
    c fan computes

end Algebraic.Cutwidth.MultiOutput.Polynomial
