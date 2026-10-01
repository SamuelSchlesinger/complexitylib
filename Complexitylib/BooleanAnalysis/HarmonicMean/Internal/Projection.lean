/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.BooleanAnalysis.HarmonicMean.Internal.Mean
import Mathlib.Logic.Equiv.Prod

/-!
# Marginal semantics of the harmonic mean transform

Splitting the cube into selected and unselected coordinates identifies the
full-cube representation with the paper's averages on projected patterns.
-/

public section

namespace Complexity.BooleanAnalysis

open Finset
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem projectionAverage_eq_coordinateMarginal_internal
    (f : (ι → Bool) → ℝ) (selected x : ι → Bool) :
    projectionAverage f selected x = coordinateMarginal f selected (fun i => x i) := by
  let e := Equiv.piEquivPiSubtypeProd (fun i => selected i = true) (fun _ => Bool)
  have he (z : ({i // selected i = true} → Bool) × ({i // selected i ≠ true} → Bool)) :
      f (fun i => if h : selected i = true then x i else z.2 ⟨i, h⟩) =
      f (fun i => if selected i then x i else e.symm z i) := by
    congr 1
    funext i
    by_cases hi : selected i = true <;> simp [e, Equiv.piEquivPiSubtypeProd, hi]
  unfold projectionAverage
  rw [← Fintype.expect_equiv e.symm _ _ he, expect_pair_internal]
  exact Fintype.expect_const (ι := {i // selected i = true} → Bool)
    (coordinateMarginal f selected (fun i => x i))

theorem expect_coordinateMarginal_internal (f : (ι → Bool) → ℝ) (selected : ι → Bool) :
    (𝔼 z, coordinateMarginal f selected z) = 𝔼 x, f x := by
  let e := Equiv.piEquivPiSubtypeProd (fun i => selected i = true) (fun _ => Bool)
  rw [← Fintype.expect_equiv e.symm (fun z => f (e.symm z)) f (fun _ => rfl),
    expect_pair_internal]
  rfl

theorem harmonicTransform_eq_harmonicMean_coordinateMarginal_internal
    (f : (ι → Bool) → ℝ) (selected : ι → Bool) :
    harmonicTransform f selected = harmonicMean (coordinateMarginal f selected) := by
  classical
  let e := Equiv.piEquivPiSubtypeProd (fun i => selected i = true) (fun _ => Bool)
  have he (z : ({i // selected i = true} → Bool) × ({i // selected i ≠ true} → Bool)) :
      projectionAverage f selected (e.symm z) = coordinateMarginal f selected z.1 := by
    rw [projectionAverage_eq_coordinateMarginal_internal]
    congr 1
    funext i
    simp [e, Equiv.piEquivPiSubtypeProd, i.property]
  rw [harmonicTransform, ← harmonicMean_equiv_internal e.symm]
  simp_rw [he]
  simp [harmonicMean, expect_pair_internal]

end Complexity.BooleanAnalysis
