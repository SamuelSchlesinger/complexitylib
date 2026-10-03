/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Defs
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Probability.Internal

/-!
# Finite probability weights and statistical distance

Probability weights remain normalized under marginalization and
deterministic maps. Their total variation distance lies in `[0,1]`, obeys
the triangle inequality, and contracts under deterministic maps. For equal
total mass, a distance bound is equivalent to the same bound on every
finite test. These results connect weighted conditional-source arguments
to the existing extractor contracts phrased using tests.
-/

public section

namespace Algebraic.Cutwidth.Extractor

/-- A normalized nonnegative weighting has a point of positive mass. -/
theorem IsProbabilityWeight.exists_pos {α : Type*} [Fintype α] {p : α → ℝ}
    (hp : IsProbabilityWeight p) : ∃ x, 0 < p x :=
  Internal.probabilityWeight_exists_pos hp

/-- No point of a finite probability distribution has mass greater than one. -/
theorem IsProbabilityWeight.le_one {α : Type*} [Fintype α] {p : α → ℝ}
    (hp : IsProbabilityWeight p) (x : α) : p x ≤ 1 :=
  Internal.probabilityWeight_le_one hp x

/-- Taking the first marginal preserves finite probability weights. -/
theorem IsProbabilityWeight.first {α β : Type*} [Fintype α] [Fintype β]
    {p : α × β → ℝ} (hp : IsProbabilityWeight p) : IsProbabilityWeight (firstWeight p) :=
  Internal.probabilityWeight_first hp

/-- A deterministic image counts all source occurrences and preserves normalization. -/
theorem IsProbabilityWeight.map {α β : Type*} [Fintype α] [Fintype β]
    {p : α → ℝ} (hp : IsProbabilityWeight p) (f : α → β) :
    IsProbabilityWeight (mapWeight f p) :=
  Internal.probabilityWeight_map hp f

/-- Uniform weights on a nonempty finite type form a probability distribution. -/
theorem isProbabilityWeight_uniform (α : Type*) [Fintype α] [Nonempty α] :
    IsProbabilityWeight (uniformWeight α) :=
  Internal.probabilityWeight_uniform α

/-- The identity map preserves every finite weighting. -/
theorem mapWeight_id {α : Type*} [Fintype α] (p : α → ℝ) : mapWeight id p = p :=
  Internal.mapWeight_id p

/-- An equivalence transports each point mass to its unique image. -/
theorem mapWeight_equiv_apply {α β : Type*} [Fintype α]
    (e : α ≃ β) (p : α → ℝ) (y : β) : mapWeight e p y = p (e.symm y) :=
  Internal.mapWeight_equiv_apply e p y

/-- Deterministic pushforwards compose, including when either map identifies points. -/
theorem mapWeight_comp {α β γ : Type*} [Fintype α] [Fintype β]
    (p : α → ℝ) (f : α → β) (g : β → γ) :
    mapWeight g (mapWeight f p) = mapWeight (fun x => g (f x)) p :=
  Internal.mapWeight_comp p f g

/-- The first marginal is the deterministic image under the first projection. -/
theorem mapWeight_fst {α β : Type*} [Fintype α] [Fintype β]
    (p : α × β → ℝ) : mapWeight Prod.fst p = firstWeight p :=
  Internal.mapWeight_fst p

/-- The second marginal sums over every first-coordinate occurrence. -/
theorem mapWeight_snd_apply {α β : Type*} [Fintype α] [Fintype β]
    (p : α × β → ℝ) (b : β) : mapWeight Prod.snd p b = ∑ a, p (a, b) :=
  Internal.mapWeight_snd_apply p b

/-- A point-mass cap cannot exceed the size of the finite sampling space. -/
theorem CappedWeight.card_le {α : Type*} [Fintype α] {p : α → ℝ} {K : Nat}
    (cap : CappedWeight p K) (hp : IsProbabilityWeight p) : K ≤ Fintype.card α :=
  Internal.cappedWeight_card_le hp cap

/-- A normalized source with full possible min-entropy is exactly uniform. -/
theorem CappedWeight.eq_uniform {α : Type*} [Fintype α] {p : α → ℝ}
    (cap : CappedWeight p (Fintype.card α)) (hp : IsProbabilityWeight p) :
    p = uniformWeight α :=
  Internal.cappedWeight_eq_uniform cap hp

/-- Total variation is nonnegative, including for unnormalized weights. -/
theorem weightDist_nonneg {α : Type*} [Fintype α] (p q : α → ℝ) :
    0 ≤ weightDist p q :=
  Internal.weightDist_nonneg p q

/-- A weighting has zero distance from itself. -/
theorem weightDist_self {α : Type*} [Fintype α] (p : α → ℝ) : weightDist p p = 0 :=
  Internal.weightDist_self p

/-- Finite total variation is symmetric. -/
theorem weightDist_comm {α : Type*} [Fintype α] (p q : α → ℝ) :
    weightDist p q = weightDist q p :=
  Internal.weightDist_comm p q

/-- Successive repairs add their total variation errors. -/
theorem weightDist_triangle {α : Type*} [Fintype α] (p q r : α → ℝ) :
    weightDist p r ≤ weightDist p q + weightDist q r :=
  Internal.weightDist_triangle p q r

/-- Zero total variation means equality at every point. -/
theorem weightDist_eq_zero_iff {α : Type*} [Fintype α] (p q : α → ℝ) :
    weightDist p q = 0 ↔ p = q :=
  Internal.weightDist_eq_zero_iff p q

/-- Two finite probability distributions have total variation at most one. -/
theorem weightDist_le_one {α : Type*} [Fintype α] {p q : α → ℝ}
    (hp : IsProbabilityWeight p) (hq : IsProbabilityWeight q) : weightDist p q ≤ 1 :=
  Internal.weightDist_le_one hp hq

/-- Deterministic processing cannot increase total variation. -/
theorem weightDist_map_le {α β : Type*} [Fintype α] [Fintype β]
    (p q : α → ℝ) (f : α → β) : weightDist (mapWeight f p) (mapWeight f q) ≤ weightDist p q :=
  Internal.weightDist_map_le p q f

/-- Equal-mass weights differ on any finite test by at most their total variation. -/
theorem weightTestProb_sub_le_dist {α : Type*} [Fintype α] (p q : α → ℝ)
    (mass : ∑ x, p x = ∑ x, q x) (T : Finset α) :
    |weightTestProb p T - weightTestProb q T| ≤ weightDist p q :=
  Internal.weightTestProb_sub_le_dist p q mass T

/-- For equal total mass, the finite-test and total-variation bounds are equivalent. -/
theorem weightDist_le_iff_tests {α : Type*} [Fintype α] (p q : α → ℝ)
    (mass : ∑ x, p x = ∑ x, q x) {ε : ℝ} :
    weightDist p q ≤ ε ↔ ∀ T : Finset α,
      |weightTestProb p T - weightTestProb q T| ≤ ε :=
  Internal.weightDist_le_iff_tests p q mass

open scoped Classical in
/-- Testing a deterministic image is the same as testing its preimage. -/
theorem weightTestProb_map {α β : Type*} [Fintype α] (p : α → ℝ)
    (f : α → β) (T : Finset β) :
    weightTestProb (mapWeight f p) T = ∑ x, if f x ∈ T then p x else 0 :=
  Internal.weightTestProb_map p f T

open scoped Classical in
/-- Two deterministic observations differ in total variation by at most
their disagreement probability under the same source. -/
theorem weightDist_map_map_le {α β : Type*} [Fintype α] [Fintype β]
    {p : α → ℝ} (hp : IsProbabilityWeight p) (f g : α → β) :
    weightDist (mapWeight f p) (mapWeight g p) ≤ ∑ x with f x ≠ g x, p x :=
  Internal.weightDist_map_map_le hp f g

end Algebraic.Cutwidth.Extractor
