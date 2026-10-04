/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Sampler.Amplification.Defs

/-!
# Reindexing outer seeds and candidate lists

Bijections of either sampler index preserve every all-candidate hitting
event. The bad-input sets and the source-weighted failure bound therefore
remain unchanged.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

theorem allHitSeeds_reindex_card {α Outer Outer' Candidate Candidate' Ω : Type*}
    [Fintype Outer] [Fintype Outer']
    (S : α → Outer → Candidate → Ω) (outer : Outer' ≃ Outer)
    (candidate : Candidate' ≃ Candidate) (T : Finset Ω) (x : α) :
    (allHitSeeds (fun x y z => S x (outer y) (candidate z)) T x).card =
      (allHitSeeds S T x).card := by
  classical
  apply Finset.card_bij (fun y _ => outer y)
  · intro y hy
    simp only [allHitSeeds, Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
    intro z
    simpa only [candidate.apply_symm_apply] using hy (candidate.symm z)
  · intro y _ z _ equal
    exact outer.injective equal
  · intro y hy
    refine ⟨outer.symm y, ?_, outer.apply_symm_apply y⟩
    simp only [allHitSeeds, Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
    intro z
    simpa only [outer.apply_symm_apply] using hy (candidate z)

theorem somewhereSampler_reindex {α Outer Outer' Candidate Candidate' Ω : Type*}
    [Fintype α] [Fintype Outer] [Fintype Outer'] [Fintype Ω]
    {S : α → Outer → Candidate → Ω} {L ε δ : ℝ}
    (sample : SomewhereSampler S L ε δ) (outer : Outer' ≃ Outer)
    (candidate : Candidate' ≃ Candidate) :
    SomewhereSampler (fun x y z => S x (outer y) (candidate z)) L ε δ := by
  intro T small p nonnegative probability cap
  have events : somewhereBadInputs (fun x y z => S x (outer y) (candidate z)) T ε =
      somewhereBadInputs S T ε := by
    apply Finset.ext
    intro x
    simp only [somewhereBadInputs, Finset.mem_filter, Finset.mem_univ, true_and,
      allHitSeeds_reindex_card S outer candidate T x, Fintype.card_congr outer]
  rw [events]
  exact sample T small p nonnegative probability cap

end Algebraic.Cutwidth.Extractor.Internal
