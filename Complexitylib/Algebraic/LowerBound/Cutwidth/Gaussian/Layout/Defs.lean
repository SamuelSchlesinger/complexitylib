/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Prod.Lex
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Orderings by real scores

A real score on a finite type orders it lexicographically by the score and then by a
fixed enumeration. `scoreKey X v` is the number of elements strictly below `v` in this
order, an injective natural-number key whose prefixes are lower sets for the score.

`gaussianCutwidthCoefficient = (3/π)(3 - 2√2) ≈ 0.16384` is the prefix-cut coefficient
achieved by Gaussian distance-kernel layouts of cubic graphs, below the `1/6` of the
Monien–Preis and Fomin–Høie bounds.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Gaussian

open scoped Classical

variable {W : Type} [Fintype W]

/-- The lexicographic position of a vertex: its score, then its enumeration index. -/
noncomputable def scoreRank (X : W → ℝ) (v : W) : ℝ ×ₗ ℕ :=
  toLex (X v, (Fintype.equivFin W v : ℕ))

/-- The number of vertices strictly below `v` in the lexicographic score order. -/
noncomputable def scoreKey (X : W → ℝ) (v : W) : ℕ :=
  (Finset.univ.filter fun w => scoreRank X w < scoreRank X v).card

/-- The cubic cutwidth coefficient of the Gaussian layout, `(3/π)(3 - 2√2)`. -/
noncomputable def gaussianCutwidthCoefficient : ℝ :=
  3 / Real.pi * (3 - 2 * Real.sqrt 2)

end Algebraic.Cutwidth.Gaussian
