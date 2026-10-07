/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.RestrictionCylinders
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.RestrictionKeepClause
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.RestrictionProbability
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.CylinderProbability

/-!
# Unrestricted depth-three lower bound: restriction path data

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DepthThree/RestrictionPathData.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical proofs are retained.
-/

@[expose] public section

namespace Complexity

universe uDepth1 uDepth2

noncomputable section

open scoped BigOperators Classical

namespace DepthThreeLowerBound

variable {V : Type uDepth1} {I : Type uDepth2} [instFintypeV : Fintype V] [instFintypeI : Fintype I]

/-- There is an extension of the restriction violating every clause on the path. -/
def pathCompatible (C : I → Clause V) (σ : Restriction V) (P : List I) : Prop :=
  ∃ z : Cube (Live σ), ∀ i ∈ P, (C i).violation (fill σ z) = true

/-- Choose a witnessing assignment for a compatible path, or all false otherwise. -/
def pathCenter (C : I → Clause V) (σ : Restriction V) (P : List I) : Cube (Live σ) :=
  if h : pathCompatible C σ P then Classical.choose h else fun _ => false

omit [Fintype V] [Fintype I] in
theorem pathCenter_support
    {V : Type uDepth1}
    {I : Type uDepth2}


    (C : I → Clause V) (σ : Restriction V) (P : List I)
    (h : pathCompatible C σ P) :
    ∀ i ∈ P, (C i).violation (fill σ (pathCenter C σ P)) = true := by
  unfold pathCenter
  rw [dite_eq_left h]
  exact Classical.choose_spec h
omit [Fintype V] [Fintype I] in
@[simp] theorem pathCompatible_nil
    {V : Type uDepth1}
    {I : Type uDepth2}


    (C : I → Clause V) (σ : Restriction V) :
    pathCompatible C σ [] := by
  exact ⟨fun _ => false, by simp⟩
/-- Live variables revealed by a prefix of the clause path. -/
def pathPrefixSet (C : I → Clause V) (σ : Restriction V) (P : List I)
    (h : Fin P.length) : Finset V :=
  revealed (fun i => (C i).scope) (liveSet σ) (P.take (h.val + 1))

/-- Live variables revealed by the complete clause path. -/
def pathFinalSet (C : I → Clause V) (σ : Restriction V) (P : List I) : Finset V :=
  revealed (fun i => (C i).scope) (liveSet σ) P

/-- The revealed variables viewed as elements of the restriction's live set. -/
def pathLiveSet (C : I → Clause V) (σ : Restriction V) (P : List I) :
    Finset (Live σ) :=
  Finset.univ.filter fun v => v.val ∈ pathFinalSet C σ P

/-- The covered-clause count at a path prefix under its witnessing assignment. -/
def pathCoveredCount (C : I → Clause V) (σ : Restriction V) (P : List I)
    (h : Fin P.length) : ℕ :=
  coveredCount (fun i => (C i).scope) (liveSet σ)
    (fun i => (C i).violation (fill σ (pathCenter C σ P))) (pathPrefixSet C σ P h)

/-- The product of reciprocal covered-clause counts along the path. -/
def pathWeight (C : I → Clause V) (σ : Restriction V) (P : List I) : ℝ :=
  ∏ h : Fin P.length, (pathCoveredCount C σ P h : ℝ)⁻¹

/-- Sum the weights of compatible paths of a fixed length. -/
def pathCost (C : I → Clause V) (b : ℕ) (σ : Restriction V) (j : ℕ) : ℝ :=
  ∑ P ∈ paths (fun i => (C i).scope) (liveSet σ) b j,
    if pathCompatible C σ P then pathWeight C σ P else 0

/-- Sum the compatible-path costs over all allowed lengths. -/
def restrictionCost (C : I → Clause V) (b : ℕ) (σ : Restriction V) : ℝ :=
  ∑ j ∈ Finset.range (Fintype.card V / (b + 1) + 1), pathCost C b σ j

theorem pathWeight_nonneg (C : I → Clause V) (σ : Restriction V) (P : List I) :
    0 ≤ pathWeight C σ P := by
  exact Finset.prod_nonneg fun h _ => inv_nonneg.mpr (Nat.cast_nonneg _)

theorem pathCost_nonneg (C : I → Clause V) (b : ℕ) (σ : Restriction V) (j : ℕ) :
    0 ≤ pathCost C b σ j := by
  apply Finset.sum_nonneg
  intro P hP
  split
  · exact pathWeight_nonneg C σ P
  · exact le_rfl

theorem restrictionCost_nonneg (C : I → Clause V) (b : ℕ) (σ : Restriction V) :
    0 ≤ restrictionCost C b σ :=
  Finset.sum_nonneg fun j _ => pathCost_nonneg C b σ j

@[simp] theorem pathWeight_nil (C : I → Clause V) (σ : Restriction V) :
    pathWeight C σ [] = 1 := by simp [pathWeight]

@[simp] theorem pathCost_zero (C : I → Clause V) (b : ℕ) (σ : Restriction V) :
    pathCost C b σ 0 = 1 := by
  simp [pathCost, paths_zero]

omit [Fintype I] in
theorem pathPrefixSet_subset_final
    {V : Type uDepth1}
    {I : Type uDepth2}
    [instFintypeV : Fintype V]

    (C : I → Clause V) (σ : Restriction V)
    (P : List I) (h : Fin P.length) :
    pathPrefixSet C σ P h ⊆ pathFinalSet C σ P :=
  revealed_mono (fun i => (C i).scope) (liveSet σ) (List.take_subset _ _)
theorem pathCoveredCount_pos (C : I → Clause V) (b : ℕ) (σ : Restriction V)
    {n : ℕ} {P : List I}
    (hP : P ∈ paths (fun i => (C i).scope) (liveSet σ) b n)
    (hc : pathCompatible C σ P) (h : Fin P.length) :
    0 < pathCoveredCount C σ P h := by
  have hk : h.val + 1 ≤ n := by
    rw [← length_of_mem_paths hP]
    exact Nat.succ_le_of_lt h.isLt
  have hpref := take_mem_paths (fun i => (C i).scope) (liveSet σ) b hP hk
  have hs : pathNumerator
      (fun i => (C i).violation (fill σ (pathCenter C σ P)))
      (P.take (h.val + 1)) ≠ 0 := by
    apply (pathNumerator_ne_zero_iff _ _).mpr
    intro i hi
    exact pathCenter_support C σ P hc i ((List.take_subset _ _) hi)
  have hle := length_le_coveredCount_of_support (fun i => (C i).scope)
    (liveSet σ) b (fun i => (C i).violation (fill σ (pathCenter C σ P))) hpref hs
  rw [length_of_mem_paths hpref] at hle
  exact (Nat.succ_pos h.val).trans_le hle

omit [Fintype I] in
theorem pathLiveSet_image
    {V : Type uDepth1}
    {I : Type uDepth2}
    [instFintypeV : Fintype V]

    (C : I → Clause V) (σ : Restriction V) (P : List I) :
    (pathLiveSet C σ P).image Subtype.val = pathFinalSet C σ P := by
  ext v
  constructor
  · intro hv
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
    exact (Finset.mem_filter.mp hw).2
  · intro hv
    have ht : v ∈ liveSet σ := revealed_subset (fun i => (C i).scope) (liveSet σ) P hv
    have hσ : σ v = none := by simpa [liveSet] using ht
    exact Finset.mem_image.mpr ⟨⟨v, hσ⟩, by simp [pathLiveSet, hv], rfl⟩
omit instFintypeI in
theorem pathLiveSet_card (C : I → Clause V) (σ : Restriction V) (P : List I) :
    (pathLiveSet C σ P).card = (pathFinalSet C σ P).card := by
  rw [← pathLiveSet_image C σ P]
  exact (Finset.card_image_of_injective _ Subtype.val_injective).symm

omit instFintypeI in
theorem path_support_iff_live_cylinder (C : I → Clause V) (σ : Restriction V)
    (P : List I) (hn : ∀ i ∈ P, (C i).Normalized) (hc : pathCompatible C σ P)
    (x : Cube (Live σ)) :
    (∀ i ∈ P, (C i).violation (fill σ x) = true) ↔
      ∀ v ∈ pathLiveSet C σ P, x v = pathCenter C σ P v := by
  rw [simultaneous_restricted_violation_iff C σ (liveSet σ)
    (by intro v; simp [liveSet]) P x (pathCenter C σ P) hn
    (pathCenter_support C σ P hc)]
  constructor
  · intro h v hv
    have hval : v.val ∈ pathFinalSet C σ P := (Finset.mem_filter.mp hv).2
    simpa using h v.val hval
  · intro h v hv
    have ht : v ∈ liveSet σ := revealed_subset (fun i => (C i).scope) (liveSet σ) P hv
    have hσ : σ v = none := by simpa [liveSet] using ht
    have hv' : (⟨v, hσ⟩ : Live σ) ∈ pathLiveSet C σ P := by
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩
    simpa [fill, hσ] using h ⟨v, hσ⟩ hv'

theorem path_cylinder_probability (C : I → Clause V) (σ : Restriction V)
    (P : List I) (hn : ∀ i ∈ P, (C i).Normalized) (hc : pathCompatible C σ P) :
    finiteAvg (fun x : Cube (Live σ) =>
      indicator (decide (∀ i ∈ P, (C i).violation (fill σ x) = true))) =
      ((2 : ℝ) ^ (pathFinalSet C σ P).card)⁻¹ := by
  simp_rw [path_support_iff_live_cylinder C σ P hn hc]
  calc
    _ = ((2 : ℝ) ^ (pathLiveSet C σ P).card)⁻¹ := by
      have havg (inst₁ inst₂ : Fintype (Cube (Live σ)))
          (f g : Cube (Live σ) → ℝ) (hfg : ∀ x, f x = g x) :
          @finiteAvg _ inst₁ f = @finiteAvg _ inst₂ g := by
        have hi : inst₁ = inst₂ := Subsingleton.elim _ _
        cases hi
        exact @finiteAvg_congr _ inst₁ f g hfg
      refine Eq.trans ?_
        (finiteAvg_indicator_eq_pattern (pathLiveSet C σ P) (pathCenter C σ P))
      apply havg
      intro x
      apply congrArg indicator
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq]
    _ = _ := by rw [pathLiveSet_card]

end DepthThreeLowerBound

end

end Complexity
