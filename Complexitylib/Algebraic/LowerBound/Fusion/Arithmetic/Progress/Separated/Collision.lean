/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Fusion.Arithmetic.Progress.Separated.Unit

/-!
# One-collision finite counting

The additive enrichment proof reduces to a small finite pigeonhole lemma.  If
every fiber of a map has size at most two, and all nontrivial fibers have the
same image, then identifying fibers loses at most one element.
-/

@[expose] public section

namespace Algebraic
namespace Fusion
namespace Arithmetic
namespace Progress
namespace Separated
namespace Collision

/-- A finite map with fibers of size at most two and at most one nontrivial
fiber loses at most one in the `cardinality - 1` score. -/
theorem card_sub_one_le_image
    {Domain Codomain : Type*}
    [Fintype Domain]
    [DecidableEq Domain]
    [DecidableEq Codomain]
    (map : Domain → Codomain)
    (fiber_pair : ∀ {first second other},
      first ≠ second →
        map first = map second →
          map other = map first →
            other = first ∨ other = second)
    (collisions_same : ∀ {first second third fourth},
      first ≠ second →
        map first = map second →
          third ≠ fourth →
            map third = map fourth →
              map third = map first) :
    Fintype.card Domain - 1 ≤
      (Finset.univ.image map).card - 1 + 1 := by
  classical
  by_cases injective : Function.Injective map
  · rw [Finset.card_image_of_injective _ injective, Finset.card_univ]
    omega
  · obtain ⟨first, second, sameImage, distinct⟩ :=
      Function.not_injective_iff.mp injective
    have remainingInjective : Set.InjOn map
        (↑(Finset.univ.erase second) : Set Domain) := by
      intro third thirdPresent fourth fourthPresent same
      by_contra thirdDistinctFourth
      have thirdImage : map third = map first :=
        collisions_same distinct sameImage thirdDistinctFourth same
      have thirdPair : third = first ∨ third = second :=
        fiber_pair distinct sameImage thirdImage
      have fourthImage : map fourth = map first := same.symm.trans thirdImage
      have fourthPair : fourth = first ∨ fourth = second :=
        fiber_pair distinct sameImage fourthImage
      have thirdNotSecond : third ≠ second := by
        simpa using thirdPresent
      have fourthNotSecond : fourth ≠ second := by
        simpa using fourthPresent
      rcases thirdPair with rfl | thirdIsSecond
      · rcases fourthPair with rfl | fourthIsSecond
        · exact thirdDistinctFourth rfl
        · exact fourthNotSecond fourthIsSecond
      · exact thirdNotSecond thirdIsSecond
    have remainingCard : (Finset.univ.erase second).card =
        Fintype.card Domain - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ second),
        Finset.card_univ]
    have remainingImageCard :
        ((Finset.univ.erase second).image map).card =
          (Finset.univ.erase second).card :=
      Finset.card_image_iff.mpr remainingInjective
    have remainingImageSubset :
        (Finset.univ.erase second).image map ⊆
          Finset.univ.image map :=
      (Finset.image_mono map) (Finset.erase_subset second Finset.univ)
    have cardinality : Fintype.card Domain - 1 ≤
        (Finset.univ.image map).card := by
      rw [← remainingCard, ← remainingImageCard]
      exact Finset.card_le_card remainingImageSubset
    have imagePositive : 0 < (Finset.univ.image map).card :=
      Finset.card_pos.mpr ⟨map first,
        Finset.mem_image.mpr ⟨first, Finset.mem_univ first, rfl⟩⟩
    omega

end Collision
end Separated
end Progress
end Arithmetic
end Fusion
end Algebraic
