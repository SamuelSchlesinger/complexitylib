/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Coupling.Factored.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Affine.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Conditional.Defs
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Coupling.Factored.Internal.Basic
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Coupling
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Probability
import Mathlib.Logic.Equiv.Prod

/-!
# Repairing a distinguished coordinate while preserving the factored law

The checked correlated marginal-replacement construction applies to each
already normalized right kernel, including kernels under zero-mass
transcripts. Exact distance averages then recover the global retained
coordinate discrepancy with the unchanged left kernel.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

private theorem uniform_right_row {B Q : Type*} [Fintype B] [Fintype Q]
    (r : B → ℝ) (q : B → Q) (hr : IsProbabilityWeight r) :
    ∃ r' : B × Q → ℝ, IsProbabilityWeight r' ∧
      mapWeight Prod.fst r' = r ∧ mapWeight Prod.snd r' = uniformWeight Q ∧
      weightDist (mapWeight (fun b => (b, q b)) r) r' =
        weightDist (mapWeight q r) (uniformWeight Q) := by
  obtain ⟨b, _⟩ := hr.exists_pos
  let : Nonempty Q := ⟨q b⟩
  let p := mapWeight (fun b => (q b, b)) r
  have hp : IsProbabilityWeight p := hr.map _
  have first : firstWeight p = mapWeight q r := by
    rw [← mapWeight_fst, mapWeight_comp]
  have second : mapWeight Prod.snd p = r := by
    rw [mapWeight_comp]
    exact mapWeight_id r
  obtain ⟨p', hp', uniform, preserve, distance⟩ :=
    exists_joint_marginal_replacement hp (isProbabilityWeight_uniform Q)
  let e := Equiv.prodComm Q B
  refine ⟨mapWeight e p', hp'.map e, ?_, ?_, ?_⟩
  · rw [mapWeight_comp]
    change mapWeight Prod.snd p' = r
    funext b
    rw [mapWeight_snd_apply, preserve, ← mapWeight_snd_apply, second]
  · rw [mapWeight_comp]
    exact (mapWeight_fst p').trans uniform
  · have old : mapWeight e p = mapWeight (fun b => (b, q b)) r := by
      rw [mapWeight_comp]
      rfl
    rw [← old]
    have same : weightDist (mapWeight e p) (mapWeight e p') = weightDist p p' := by
      simp only [weightDist, mapWeight_equiv_apply]
      exact congrArg (fun s : ℝ => s / 2) (e.symm.sum_comp (fun u => |p u - p' u|))
    rw [same, distance, first]

theorem exists_factored_uniform_right_repair_rows {Z A B Q : Type*}
    [Fintype Z] [Fintype A] [Fintype B] [Fintype Q]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ) (q : Z → B → Q)
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z)) :
    ∃ r' : Z → B × Q → ℝ, (∀ z, IsProbabilityWeight (r' z)) ∧
      (∀ z, mapWeight Prod.fst (r' z) = r z) ∧
      (∀ z, mapWeight Prod.snd (r' z) = uniformWeight Q) ∧
      weightDist (factoredWeight w l (rightCoordinateLift r q)) (factoredWeight w l r') =
        weightDist (retainedSeedWeight w r q)
          (uniformSecondWeight (retainedSeedWeight w r q)) := by
  choose r' probability first second distance using fun z => uniform_right_row (r z) (q z) (hr z)
  refine ⟨r', probability, first, second, ?_⟩
  rw [factoredWeight_dist_right w l _ _ hw.1 hl,
      retainedSeedWeight_dist_eq_sum w r q hw.1 hr]
  apply Finset.sum_congr rfl
  intro z _
  rw [show rightCoordinateLift r q z = mapWeight (fun b => (b, q z b)) (r z) from rfl,
      distance]

theorem exists_factored_uniform_right_repair {Z A B Q : Type*}
    [Fintype Z] [Fintype A] [Fintype B] [Fintype Q]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ) (q : Z → B → Q)
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z)) :
    ∃ r' : Z → B × Q → ℝ, (∀ z, IsProbabilityWeight (r' z)) ∧
      (∀ z b, w z * mapWeight Prod.fst (r' z) b = w z * r z b) ∧
      (∀ z u, w z * mapWeight Prod.snd (r' z) u = w z * uniformWeight Q u) ∧
      weightDist (factoredWeight w l (rightCoordinateLift r q)) (factoredWeight w l r') =
        weightDist (retainedSeedWeight w r q)
          (uniformSecondWeight (retainedSeedWeight w r q)) := by
  obtain ⟨r', probability, first, second, distance⟩ :=
    exists_factored_uniform_right_repair_rows w l r q hw hl hr
  exact ⟨r', probability, fun z b => by rw [first], fun z u => by rw [second], distance⟩

end Algebraic.Cutwidth.Extractor.Internal
