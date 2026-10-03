/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Defs

/-!
# Conditional finite weights and independent uniform extension

A conditional row divides by its first marginal. Zero-mass rows use the
uniform distribution, so every row of a probability law is normalized when
the second alphabet is nonempty. Uniform extension retains an arbitrary
first-coordinate law and samples a fresh independent second coordinate.
Uniformizing a joint law means keeping its actual first marginal.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Extractor

open scoped Classical

/-- Normalize a row, completing zero-mass rows by the uniform weighting. -/
noncomputable def conditionalWeight {α β : Type*} [Fintype β]
    (p : α × β → ℝ) (a : α) (b : β) : ℝ :=
  if firstWeight p a = 0 then uniformWeight β b else p (a, b) / firstWeight p a

/-- Append an independent uniform second coordinate to a supplied first-coordinate weighting. -/
noncomputable def uniformExtensionWeight (β : Type*) [Fintype β]
    {α : Type*} (w : α → ℝ) (ab : α × β) : ℝ :=
  w ab.1 * uniformWeight β ab.2

/-- Keep the actual first marginal of a joint weighting and uniformize the second coordinate. -/
noncomputable def uniformSecondWeight {α β : Type*} [Fintype β]
    (p : α × β → ℝ) : α × β → ℝ :=
  uniformExtensionWeight β (firstWeight p)

end Algebraic.Cutwidth.Extractor
