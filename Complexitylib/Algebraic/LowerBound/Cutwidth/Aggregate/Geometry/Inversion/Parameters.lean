/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Entropy.OneWay

/-!
# Constants for the inversion rank and entropy bound

Combining independent nonlinear output components, constant output summaries, and
affine pairing yields coefficient `(3+2c)/(2+c)`, where `c=1-H₂(1/4)`. This is
approximately `1.54311234736`, strictly above three halves.
-/

@[expose] public section

namespace Algebraic.Aggregate.Geometry.Inversion

open Cutwidth.Aggregate.Geometry

/-- Leading gate coefficient from independent components and biased messages. -/
noncomputable def gateCoefficient : ℝ := (3 + 2 * Entropy.bitSaving) / (2 + Entropy.bitSaving)

/-- The finite additive loss contributed by a two-dimensional affine restriction. -/
noncomputable def constantPenalty : ℝ := 4 * Entropy.bitSaving / (2 + Entropy.bitSaving)

/-- Independent nonlinear outputs strictly improve the three-halves coefficient. -/
theorem three_halves_lt_gateCoefficient : (3 / 2 : ℝ) < gateCoefficient := by
  unfold gateCoefficient
  apply (lt_div_iff₀ (by linarith [Entropy.bitSaving_pos])).mpr
  linarith [Entropy.bitSaving_pos]

/-- The present rank and entropy combination gives a coefficient below two. -/
theorem gateCoefficient_lt_two : gateCoefficient < 2 := by
  unfold gateCoefficient
  apply (div_lt_iff₀ (by linarith [Entropy.bitSaving_pos])).mpr
  linarith

/-- The exact finite penalty is positive. -/
theorem constantPenalty_pos : 0 < constantPenalty := by
  exact div_pos (mul_pos (by norm_num) Entropy.bitSaving_pos)
    (by linarith [Entropy.bitSaving_pos])

end Algebraic.Aggregate.Geometry.Inversion
