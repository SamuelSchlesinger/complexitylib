/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Defs
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Coupling.Internal.Maximal
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Coupling.Internal.Lifting
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Coupling.Internal.Projection

/-!
# Finite maximal coupling and correlated marginal replacement

Two finite probability weights admit a coupling whose probability of unequal
coordinates is exactly their total variation distance. The construction
places their common pointwise mass on the diagonal and couples the disjoint
residual weights.

The coupling can be lifted while preserving an arbitrary existing joint
distribution. Replacing its first marginal then changes that coordinate
with probability exactly the distance between the old and new marginals.
No independence of the original coordinates is assumed.
Projecting the coupling to the new pair preserves the second marginal and
changes the joint law by exactly the original marginal distance.
The replacement kernel makes the new first coordinate conditionally
independent of the old second coordinate given the old first coordinate.

This finite coupling and lifting layer supplies the probability construction
needed in the conditional Markov extension of Chattopadhyay--Goodman--Liao,
Lemma 4.19, which credits Li's 2015 Lemma 3.20:
<https://eccc.weizmann.ac.il/report/2021/075/download/>.
The extension across an external conditioning variable and preservation of
its full Markov factorization are separate from the identities proved here.
-/

public section

namespace Algebraic.Cutwidth.Extractor

open scoped Classical

/-- A maximal finite coupling has the prescribed marginals and disagreement
probability exactly equal to total variation distance. -/
theorem exists_maximal_coupling {α : Type*} [Fintype α] {p q : α → ℝ}
    (hp : IsProbabilityWeight p) (hq : IsProbabilityWeight q) :
    ∃ r : α × α → ℝ, IsProbabilityWeight r ∧
      (∀ a, ∑ b, r (a, b) = p a) ∧ (∀ b, ∑ a, r (a, b) = q b) ∧
        (∑ z with z.1 ≠ z.2, r z) = weightDist p q :=
  Internal.exists_maximal_coupling hp hq

/-- Lift a maximal coupling through the old first coordinate's conditional
kernel. The final identity states conditional independence and also covers
old first-coordinate fibers of mass zero. -/
theorem exists_marginal_replacement_kernel {α β : Type*} [Fintype α] [Fintype β]
    {p : α × β → ℝ} {q : α → ℝ} (hp : IsProbabilityWeight p)
    (hq : IsProbabilityWeight q) :
    ∃ ρ : (α × β) × α → ℝ, IsProbabilityWeight ρ ∧
      (∀ z, ∑ a', ρ (z, a') = p z) ∧ (∀ a', ∑ z, ρ (z, a') = q a') ∧
        (∑ z with z.1.1 ≠ z.2, ρ z) = weightDist (firstWeight p) q ∧
          ∀ a b a', firstWeight p a * ρ ((a, b), a') =
            p (a, b) * (∑ b', ρ ((a, b'), a')) :=
  Internal.exists_marginal_replacement_kernel hp hq

/-- Couple a new first coordinate with an existing correlated pair, keeping
the full original joint law and the prescribed new marginal. -/
theorem exists_marginal_replacement_coupling {α β : Type*} [Fintype α] [Fintype β]
    {p : α × β → ℝ} {q : α → ℝ} (hp : IsProbabilityWeight p)
    (hq : IsProbabilityWeight q) :
    ∃ ρ : (α × β) × α → ℝ, IsProbabilityWeight ρ ∧
      (∀ z, ∑ a', ρ (z, a') = p z) ∧ (∀ a', ∑ z, ρ (z, a') = q a') ∧
        (∑ z with z.1.1 ≠ z.2, ρ z) = weightDist (firstWeight p) q :=
  Internal.exists_marginal_replacement_coupling hp hq

/-- A prescribed first marginal can replace the old one while preserving
the second marginal, at exactly the original marginal's distance. -/
theorem exists_joint_marginal_replacement {α β : Type*} [Fintype α] [Fintype β]
    {p : α × β → ℝ} {q : α → ℝ} (hp : IsProbabilityWeight p)
    (hq : IsProbabilityWeight q) :
    ∃ p' : α × β → ℝ, IsProbabilityWeight p' ∧ firstWeight p' = q ∧
      (∀ b, ∑ a, p' (a, b) = ∑ a, p (a, b)) ∧
        weightDist p p' = weightDist (firstWeight p) q :=
  Internal.exists_joint_marginal_replacement hp hq

end Algebraic.Cutwidth.Extractor
