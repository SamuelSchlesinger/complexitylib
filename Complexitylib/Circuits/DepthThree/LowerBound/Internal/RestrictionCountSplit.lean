/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.RestrictionExpansion

/-!
# Unrestricted depth-three lower bound: restriction count split

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DepthThree/RestrictionCountSplit.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical proofs are retained.
-/

@[expose] public section

namespace Complexity

universe uDepth1 uDepth2

noncomputable section

open scoped Classical

namespace DepthThreeLowerBound

variable {V : Type uDepth1} {I : Type uDepth2} [instFintypeI : Fintype I]

/-- Clauses classified as intermediate at the current revealed set. -/
def intermediateIndices (scope : I → Finset V) (T : Finset V) (b : ℕ)
    (U : Finset V) : Finset I :=
  Finset.univ.filter fun i =>
    0 < (residual scope T U i).card ∧ (residual scope T U i).card ≤ b

@[simp] theorem mem_intermediateIndices (scope : I → Finset V) (T : Finset V)
    (b : ℕ) (U : Finset V) (i : I) :
    i ∈ intermediateIndices scope T b U ↔
      0 < (residual scope T U i).card ∧ (residual scope T U i).card ≤ b := by
  simp [intermediateIndices]

/-- The number of intermediate clauses satisfying the selection condition. -/
def intermediateCount (scope : I → Finset V) (T : Finset V) (b : ℕ)
    (violation : I → Bool) (U : Finset V) : ℕ :=
  ((intermediateIndices scope T b U).filter fun i => violation i = true).card

theorem easyCount_eq_covered_add_intermediate (scope : I → Finset V)
    (T : Finset V) (b : ℕ) (violation : I → Bool) (U : Finset V) :
    easyCount scope T b violation U = coveredCount scope T violation U +
      intermediateCount scope T b violation U := by
  let covered : Finset I := Finset.univ.filter fun i =>
    residual scope T U i = ∅ ∧ violation i = true
  let middle := (intermediateIndices scope T b U).filter fun i => violation i = true
  have hd : Disjoint covered middle := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    have he : residual scope T U i = ∅ := (Finset.mem_filter.mp hi).2.1
    have hp : 0 < (residual scope T U i).card :=
      ((mem_intermediateIndices scope T b U i).mp (Finset.mem_filter.mp hj).1).1
    rw [he, Finset.card_empty] at hp
    exact Nat.not_lt_zero _ hp
  have hu : (Finset.univ.filter fun i =>
      (residual scope T U i).card ≤ b ∧ violation i = true) = covered ∪ middle := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
      covered, middle, mem_intermediateIndices]
    constructor
    · rintro ⟨hle, hv⟩
      by_cases he : residual scope T U i = ∅
      · exact Or.inl ⟨he, hv⟩
      · have hp : 0 < (residual scope T U i).card :=
          Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr he)
        exact Or.inr ⟨⟨hp, hle⟩, hv⟩
    · rintro (⟨he, hv⟩ | ⟨⟨hp, hle⟩, hv⟩)
      · exact ⟨by rw [he]; simp, hv⟩
      · exact ⟨hle, hv⟩
  change (Finset.univ.filter fun i =>
      (residual scope T U i).card ≤ b ∧ violation i = true).card =
    covered.card + middle.card
  rw [hu, Finset.card_union_of_disjoint hd]

omit [Fintype I] in
theorem subtype_filter_card
    {I : Type uDepth2}

    (s : Finset I) (p : I → Prop) [DecidablePred p] :
    ((Finset.univ : Finset s).filter fun i => p i.val).card = (s.filter p).card := by
  let a := (Finset.univ : Finset s).filter fun i => p i.val
  have ha : a.image Subtype.val = s.filter p := by
    ext i
    constructor
    · intro hi
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
      exact Finset.mem_filter.mpr ⟨j.property, (Finset.mem_filter.mp hj).2⟩
    · intro hi
      obtain ⟨his, hip⟩ := Finset.mem_filter.mp hi
      exact Finset.mem_image.mpr ⟨⟨i, his⟩, by simp [a, hip], rfl⟩
  rw [← ha]
  exact (Finset.card_image_of_injective a Subtype.val_injective).symm
end DepthThreeLowerBound

end

end Complexity
