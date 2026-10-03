/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Conditional.Defs
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Conditional.Internal

/-!
# Conditioning finite sources without discarding zero-mass rows

Every row is normalized, with a uniform completion at null events. Exact
factorization recovers the original joint law. Total variation from a fresh
uniform output equals the average conditional distance, retaining the actual
first marginal. These identities support finite leakage and independence
merging without a pointwise conditional entropy assumption.
-/

public section

namespace Algebraic.Cutwidth.Extractor

/-- Multiplying a conditional row by its marginal recovers each original point mass. -/
theorem conditionalWeight_factor {α β : Type*} [Fintype β]
    (p : α × β → ℝ) (nonnegative : ∀ ab, 0 ≤ p ab) (a : α) (b : β) :
    firstWeight p a * conditionalWeight p a b = p (a, b) :=
  Internal.conditionalWeight_factor p nonnegative a b

/-- Every conditional row of a probability law is normalized, including null rows. -/
theorem IsProbabilityWeight.conditionalWeight {α β : Type*}
    [Fintype α] [Fintype β] [Nonempty β]
    {p : α × β → ℝ} (probability : IsProbabilityWeight p) (a : α) :
    IsProbabilityWeight (conditionalWeight p a) :=
  Internal.probabilityWeight_conditional probability a

/-- Appending an independent uniform coordinate preserves normalization. -/
theorem IsProbabilityWeight.uniformExtension {α : Type*} [Fintype α]
    {w : α → ℝ} (probability : IsProbabilityWeight w) (β : Type*) [Fintype β] [Nonempty β] :
    IsProbabilityWeight (uniformExtensionWeight β w) :=
  Internal.probabilityWeight_uniformExtension probability β

/-- Uniform extension preserves its supplied first-coordinate weighting exactly. -/
theorem firstWeight_uniformExtension {α β : Type*} [Fintype β] [Nonempty β]
    (w : α → ℝ) : firstWeight (uniformExtensionWeight β w) = w :=
  Internal.firstWeight_uniformExtension w

/-- Replacing the second coordinate by fresh uniform randomness preserves probability. -/
theorem IsProbabilityWeight.uniformSecond {α β : Type*}
    [Fintype α] [Fintype β] [Nonempty β]
    {p : α × β → ℝ} (probability : IsProbabilityWeight p) :
    IsProbabilityWeight (uniformSecondWeight p) :=
  Internal.probabilityWeight_uniformSecond probability

/-- Distance from a conditionally uniform output averages the exact row distances. -/
theorem weightDist_uniformSecond_eq {α β : Type*}
    [Fintype α] [Fintype β]
    {p : α × β → ℝ} (probability : IsProbabilityWeight p) :
    weightDist p (uniformSecondWeight p) =
      ∑ a, firstWeight p a * weightDist (conditionalWeight p a) (uniformWeight β) :=
  Internal.weightDist_uniformSecond_eq probability

/-- Processing the second coordinate separately on each row preserves the first marginal. -/
theorem firstWeight_map_fiber {α β γ : Type*}
    [Fintype α] [Fintype β] [Fintype γ]
    (p : α × β → ℝ) (f : α → β → γ) :
    firstWeight (mapWeight (fun ab => (ab.1, f ab.1 ab.2)) p) = firstWeight p :=
  Internal.firstWeight_map_fiber p f

/-- Retaining a nonnegative mixture tag averages distance from conditionally uniform output. -/
theorem weightDist_uniformSecond_tagged {ι α β : Type*}
    [Fintype ι] [Fintype α] [Fintype β]
    (w : ι → ℝ) (p : ι → α × β → ℝ) (nonnegative : ∀ i, 0 ≤ w i) :
    weightDist (fun iab : (ι × α) × β => w iab.1.1 * p iab.1.1 (iab.1.2, iab.2))
      (uniformSecondWeight (fun iab => w iab.1.1 * p iab.1.1 (iab.1.2, iab.2))) =
        ∑ i, w i * weightDist (p i) (uniformSecondWeight (p i)) :=
  Internal.weightDist_uniformSecond_tagged w p nonnegative

/-- A deterministic observation of the first coordinate pushes forward its marginal. -/
theorem firstWeight_map_first {α β γ : Type*}
    [Fintype α] [Fintype β] [Fintype γ]
    (p : α × β → ℝ) (f : α → γ) :
    firstWeight (mapWeight (fun ab => (f ab.1, ab.2)) p) =
      mapWeight f (firstWeight p) :=
  Internal.firstWeight_map_first p f

/-- Observing the first coordinate commutes with adding independent uniform randomness. -/
theorem mapWeight_uniformExtension {α β γ : Type*}
    [Fintype α] [Fintype β] (w : α → ℝ) (f : α → γ) :
    mapWeight (fun ab : α × β => (f ab.1, ab.2)) (uniformExtensionWeight β w) =
      uniformExtensionWeight β (mapWeight f w) :=
  Internal.mapWeight_uniformExtension w f

/-- Uniformizing an output commutes with every deterministic observation of its side information. -/
theorem uniformSecondWeight_map_first {α β γ : Type*}
    [Fintype α] [Fintype β] [Fintype γ]
    (p : α × β → ℝ) (f : α → γ) :
    mapWeight (fun ab => (f ab.1, ab.2)) (uniformSecondWeight p) =
      uniformSecondWeight (mapWeight (fun ab => (f ab.1, ab.2)) p) :=
  Internal.uniformSecondWeight_map_first p f

/-- Forgetting side information cannot increase the distance from an independent uniform output. -/
theorem weightDist_uniformSecond_map_first_le {α β γ : Type*}
    [Fintype α] [Fintype β] [Fintype γ]
    (p : α × β → ℝ) (f : α → γ) :
    weightDist (mapWeight (fun ab => (f ab.1, ab.2)) p)
      (uniformSecondWeight (mapWeight (fun ab => (f ab.1, ab.2)) p)) ≤
        weightDist p (uniformSecondWeight p) :=
  Internal.weightDist_uniformSecond_map_first_le p f

end Algebraic.Cutwidth.Extractor
