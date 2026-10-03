/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Conditional.Defs
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Conditional.Transport.Internal

/-!
# Tag-dependent output bijections preserve conditional uniformity

For arbitrary finite real weights, changing the output by a bijection that
depends on the retained tag commutes with replacing the output by independent
uniform randomness. The exact total variation distance is preserved.

Adding a tag-dependent mask is a special case for finite additive groups.
The tag retains its actual marginal; normalization, positivity, commutativity,
and nonempty-type assumptions are unnecessary for these identities.
-/

public section

namespace Algebraic.Cutwidth.Extractor

/-- Fiberwise bijections commute with uniformizing the output while retaining its actual tag. -/
theorem mapWeight_uniformSecond_fiberEquiv {α β γ : Type*}
    [Fintype α] [Fintype β] [Fintype γ]
    (p : α × β → ℝ) (e : α → β ≃ γ) :
    mapWeight (fun ab => (ab.1, e ab.1 ab.2)) (uniformSecondWeight p) =
      uniformSecondWeight (mapWeight (fun ab => (ab.1, e ab.1 ab.2)) p) :=
  Internal.mapWeight_uniformSecond_fiberEquiv p e

/-- A tag-dependent output equivalence preserves the exact distance from conditional uniformity. -/
theorem weightDist_uniformSecond_fiberEquiv {α β γ : Type*}
    [Fintype α] [Fintype β] [Fintype γ]
    (p : α × β → ℝ) (e : α → β ≃ γ) :
    weightDist (mapWeight (fun ab => (ab.1, e ab.1 ab.2)) p)
      (uniformSecondWeight (mapWeight (fun ab => (ab.1, e ab.1 ab.2)) p)) =
        weightDist p (uniformSecondWeight p) :=
  Internal.weightDist_uniformSecond_fiberEquiv p e

/-- Adding a tag-dependent mask commutes with uniformizing the output in any finite add group. -/
theorem mapWeight_uniformSecond_add_right {α β : Type*}
    [Fintype α] [Fintype β] [AddGroup β]
    (p : α × β → ℝ) (mask : α → β) :
    mapWeight (fun ab => (ab.1, ab.2 + mask ab.1)) (uniformSecondWeight p) =
      uniformSecondWeight (mapWeight (fun ab => (ab.1, ab.2 + mask ab.1)) p) :=
  Internal.mapWeight_uniformSecond_add_right p mask

/-- A tag-dependent additive mask preserves the exact distance from conditional uniformity. -/
theorem weightDist_uniformSecond_add_right {α β : Type*}
    [Fintype α] [Fintype β] [AddGroup β]
    (p : α × β → ℝ) (mask : α → β) :
    weightDist (mapWeight (fun ab => (ab.1, ab.2 + mask ab.1)) p)
      (uniformSecondWeight (mapWeight (fun ab => (ab.1, ab.2 + mask ab.1)) p)) =
        weightDist p (uniformSecondWeight p) :=
  Internal.weightDist_uniformSecond_add_right p mask

end Algebraic.Cutwidth.Extractor
