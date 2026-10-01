/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.BooleanAnalysis.HarmonicMean.Internal.Mean

/-!
# Reindexing coordinate projections

Transport the harmonic transform along an equivalence of finite coordinate
types. This lets results proved by induction on `Fin n` apply inside fibers.
-/

public section

namespace Complexity.BooleanAnalysis

theorem projectionAverage_reindex_internal {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (e : ι ≃ κ) (f : (κ → Bool) → ℝ)
    (s x : ι → Bool) :
    projectionAverage (fun y => f (fun j => y (e.symm j))) s x =
      projectionAverage f (fun j => s (e.symm j)) (fun j => x (e.symm j)) := by
  unfold projectionAverage
  exact Fintype.expect_equiv (Equiv.arrowCongr e (Equiv.refl Bool)) _ _ (fun _ => rfl)

theorem harmonicTransform_reindex_internal {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (e : ι ≃ κ) (f : (κ → Bool) → ℝ)
    (s : ι → Bool) :
    harmonicTransform (fun y => f (fun j => y (e.symm j))) s =
      harmonicTransform f (fun j => s (e.symm j)) := by
  unfold harmonicTransform
  change harmonicMean (fun x => projectionAverage
    (fun y => f (fun j => y (e.symm j))) s x) = _
  simp_rw [projectionAverage_reindex_internal e f s]
  exact harmonicMean_equiv_internal (Equiv.arrowCongr e (Equiv.refl Bool)) _

end Complexity.BooleanAnalysis
