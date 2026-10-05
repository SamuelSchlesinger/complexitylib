/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Compressed.LowerBound
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Family
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Gaussian

/-!
# The explicit lower bound with compressed aggregate states

The fixed explicit family keeps coefficient `4.56249…` when the logarithmic size
of a shared aggregate register is sublinear. This charges the final-state guess
and the accumulator, with no restriction on the number of special gates.
-/

public section

namespace Algebraic.Cutwidth.Aggregate.Compressed

variable {J : Type} {State : J → Type} [∀ j, CommMonoid (State j)]

/-- Any proved graph-ordering coefficient transfers to the fixed explicit family for
mixed circuits with a sublinear budget for jointly compressed aggregate states. -/
theorem sourceReductionHardFamily_eventually_lt_size_of_orderingBound {A : ℝ} (hA : 0 < A)
    (order : ∀ η : ℝ, 0 < η → ∃ C : ℝ, Multigraph.OrderingBound A η C)
    (D : Nat → Nat)
    (hD : (fun n => (D n : ℝ)) =o[Filter.atTop] (fun n => (n : ℝ)))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in Filter.atTop, ∀ (M : Type) [CommMonoid M] [Fintype M],
      ∀ c : Circuit (Algebraic.Aggregate.signature State) n 1,
      Algebraic.Aggregate.Compressed.Factorization c.program M →
      c.Computes Algebraic.Aggregate.interpretation
        (fun x _ => Extractor.sourceReductionHardFamily n x) →
      Algebraic.Aggregate.Compressed.budget M ≤ D n →
        (1 + 1 / A - ε) * n < c.size :=
  eventually_lt_size_of_orderingBound hA order Extractor.sourceReductionHardFamily D
    familyThreshold hD familyThreshold_log_isLittleO family_eventually_hard hε

/-- **The unconditional aggregate-gate extension.** The same fixed family in polynomial time
needs more than `(4.56249… - ε) n` total gates, even with arbitrary finite commutative-monoid
aggregate gates whose joint-state budget is `o(n)`, without a gate-count restriction. -/
theorem sourceReductionHardFamily_eventually_lt_size_gaussian
    (D : Nat → Nat)
    (hD : (fun n => (D n : ℝ)) =o[Filter.atTop] (fun n => (n : ℝ)))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in Filter.atTop, ∀ (M : Type) [CommMonoid M] [Fintype M],
      ∀ c : Circuit (Algebraic.Aggregate.signature State) n 1,
      Algebraic.Aggregate.Compressed.Factorization c.program M →
      c.Computes Algebraic.Aggregate.interpretation
        (fun x _ => Extractor.sourceReductionHardFamily n x) →
      Algebraic.Aggregate.Compressed.budget M ≤ D n →
        (1 + Real.pi / (3 * Real.arccos ((1 + 2 * Real.sqrt 2) / 4)) - ε) * n <
          c.size := by
  have bound := sourceReductionHardFamily_eventually_lt_size_of_orderingBound
    (State := State) (mul_pos two_pos Gaussian.frontierCoefficient_pos)
    Multigraph.exists_orderingBound_frontier D hD hε
  rwa [Gaussian.one_add_inv_two_mul_frontierCoefficient] at bound


end Algebraic.Cutwidth.Aggregate.Compressed
