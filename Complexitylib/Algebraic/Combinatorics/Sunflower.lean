/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Combinatorics.Pigeonhole
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Order.Preorder.Finite
public import Mathlib.Tactic.Ring

/-!
# The elementary sunflower bound

The Erdős--Rado induction used by the monotone CLIQUE approximation method is
formalized here for finite set families.  A `p`-sunflower is a `p`-element
subfamily whose distinct members have one common pairwise intersection.

The quantitative endpoint is the classical elementary bound

`family.card > (p - 1) ^ width * width!`.

For families whose members have size *at most* `width`, the proof partitions
the family by cardinality and applies the uniform bound to a large layer.
-/

@[expose] public section

namespace Algebraic
namespace Sunflower

noncomputable section

/-- A finite family has a common pairwise intersection `core`. -/
def IsSunflowerWithCore
    [DecidableEq α]
    (petals : Finset (Finset α))
    (core : Finset α) : Prop :=
  ∀ {left}, left ∈ petals →
    ∀ {right}, right ∈ petals →
      left ≠ right → left ∩ right = core

/-- A family contains a sunflower with exactly `p` petals. -/
def ContainsSunflower
    [DecidableEq α]
    (p : Nat)
    (family : Finset (Finset α)) : Prop :=
  ∃ petals ⊆ family, petals.card = p ∧
    ∃ core, IsSunflowerWithCore petals core

/-- Pairwise disjoint sets form a sunflower with empty core. -/
theorem isSunflowerWithCore_empty_of_pairwiseDisjoint
    [DecidableEq α]
    {petals : Finset (Finset α)}
    (disjoint : (petals : Set (Finset α)).Pairwise
      fun left right => Disjoint left right) :
    IsSunflowerWithCore petals ∅ := by
  intro left leftPresent right rightPresent different
  exact Finset.disjoint_iff_inter_eq_empty.mp
    (disjoint leftPresent rightPresent different)

/-- A subfamily inherits pairwise disjointness. -/
theorem pairwiseDisjoint_mono
    {small large : Finset (Finset α)}
    (subset : small ⊆ large)
    (disjoint : (large : Set (Finset α)).Pairwise
      fun left right => Disjoint left right) :
    (small : Set (Finset α)).Pairwise
      fun left right => Disjoint left right := by
  intro left leftPresent right rightPresent different
  exact disjoint (subset leftPresent) (subset rightPresent) different

/-- The classical uniform Erdős--Rado sunflower bound. -/
theorem containsSunflower_of_uniform
    [DecidableEq α]
    (petals : Nat)
    (two_le : 2 ≤ petals)
    (width : Nat)
    (family : Finset (Finset α))
    (uniform : ∀ set ∈ family, set.card = width)
    (large : (petals - 1) ^ width * width.factorial < family.card) :
    ContainsSunflower petals family := by
  classical
  induction width generalizing α family with
  | zero =>
      have familySubset : family ⊆ {∅} := by
        intro set present
        have cardZero := uniform set present
        simpa [Finset.card_eq_zero] using cardZero
      have cardLe : family.card ≤ 1 := by
        simpa using Finset.card_le_card familySubset
      simp only [Nat.pow_zero, Nat.factorial_zero, Nat.mul_one] at large
      omega
  | succ width inductionHypothesis =>
      let candidates := family.powerset.filter fun
          (chosen : Finset (Finset α)) =>
        (chosen : Set (Finset α)).Pairwise
          (fun left right => Disjoint left right)
      have candidatesNonempty : candidates.Nonempty := by
        refine ⟨∅, ?_⟩
        simp [candidates]
      obtain ⟨chosen, chosenMaximal⟩ :=
        candidates.exists_maximal candidatesNonempty
      have chosenCandidate : chosen ∈ candidates := chosenMaximal.1
      have chosenSubset : chosen ⊆ family := by
        simpa [candidates] using (Finset.mem_filter.mp chosenCandidate).1
      have chosenDisjoint : (chosen : Set (Finset α)).Pairwise
          (fun left right => Disjoint left right) := by
        exact (Finset.mem_filter.mp chosenCandidate).2
      by_cases enough : petals ≤ chosen.card
      · obtain ⟨selected, selectedSubset, selectedCard⟩ :=
          Finset.exists_subset_card_eq enough
        refine ⟨selected, selectedSubset.trans chosenSubset, selectedCard, ∅,
          isSunflowerWithCore_empty_of_pairwiseDisjoint
            (pairwiseDisjoint_mono selectedSubset chosenDisjoint)⟩
      · have chosenCard : chosen.card ≤ petals - 1 := by omega
        let support : Finset α := chosen.biUnion id
        have supportCard : support.card ≤ (petals - 1) * (width + 1) := by
          calc
            support.card ≤ chosen.card * (width + 1) := by
              apply Finset.card_biUnion_le_card_mul
              intro set present
              exact (uniform set (chosenSubset present)).le
            _ ≤ (petals - 1) * (width + 1) :=
              Nat.mul_le_mul_right (width + 1) chosenCard
        have meetsSupport : ∀ set ∈ family,
            (set ∩ support).Nonempty := by
          intro set setPresent
          by_contra emptyIntersection
          have disjointSupport : Disjoint set support := by
            rw [Finset.disjoint_iff_inter_eq_empty]
            exact Finset.not_nonempty_iff_eq_empty.mp emptyIntersection
          have setNonempty : set.Nonempty := by
            rw [← Finset.card_pos]
            rw [uniform set setPresent]
            omega
          have setNotChosen : set ∉ chosen := by
            intro setChosen
            have selfDisjoint : Disjoint set set := by
              exact disjointSupport.mono_right <|
                Finset.subset_biUnion_of_mem id setChosen
            exact setNonempty.ne_empty
              (disjoint_self.mp selfDisjoint)
          have insertedDisjoint :
              ((insert set chosen : Finset (Finset α)) : Set (Finset α)).Pairwise
                (fun left right => Disjoint left right) := by
            rw [Finset.coe_insert]
            refine (Set.pairwise_insert
              (s := (↑chosen : Set (Finset α))) (a := set)
              (r := fun left right : Finset α => Disjoint left right)).2 ?_
            refine ⟨chosenDisjoint, ?_⟩
            intro other otherPresent _
            have apart := disjointSupport.mono_right
              (Finset.subset_biUnion_of_mem id otherPresent)
            exact ⟨apart, apart.symm⟩
          have insertedCandidate : insert set chosen ∈ candidates := by
            rw [Finset.mem_filter]
            exact ⟨Finset.mem_powerset.mpr
              (Finset.insert_subset setPresent chosenSubset), insertedDisjoint⟩
          have reverseSubset : insert set chosen ⊆ chosen :=
            chosenMaximal.2 insertedCandidate (Finset.subset_insert set chosen)
          exact setNotChosen (reverseSubset (Finset.mem_insert_self set chosen))
        have pickExists : ∀ set, set ∈ family →
            ∃ point, point ∈ support ∧ point ∈ set := by
          intro set present
          obtain ⟨point, pointPresent⟩ := meetsSupport set present
          have both := Finset.mem_inter.mp pointPresent
          exact ⟨point, both.2, both.1⟩
        choose dependentPick pickSupport pickSet using pickExists
        have familyNonempty : family.Nonempty := by
          rw [← Finset.card_pos]
          omega
        obtain ⟨someSet, someSetPresent⟩ := familyNonempty
        have supportNonempty : support.Nonempty := by
          obtain ⟨point, pointPresent⟩ := meetsSupport someSet someSetPresent
          exact ⟨point, (Finset.mem_inter.mp pointPresent).2⟩
        let pick (set : Finset α) : α :=
          if present : set ∈ family then dependentPick set present
          else supportNonempty.choose
        have pick_mem_support : ∀ set ∈ family, pick set ∈ support := by
          intro set present
          simp only [pick, dite_eq_left present]
          exact pickSupport set present
        have pick_mem_set : ∀ set ∈ family, pick set ∈ set := by
          intro set present
          simp only [pick, dite_eq_left present]
          exact pickSet set present
        let priorBound := (petals - 1) ^ width * width.factorial
        have thresholdIdentity :
            (petals - 1) ^ (width + 1) * (width + 1).factorial =
              ((petals - 1) * (width + 1)) * priorBound := by
          simp only [priorBound, Nat.pow_succ, Nat.factorial_succ]
          ring
        have fiberLarge : support.card * priorBound < family.card := by
          calc
            support.card * priorBound ≤
                ((petals - 1) * (width + 1)) * priorBound :=
              Nat.mul_le_mul_right priorBound supportCard
            _ = (petals - 1) ^ (width + 1) *
                (width + 1).factorial := thresholdIdentity.symm
            _ < family.card := large
        obtain ⟨point, pointSupport, pointFiber⟩ :=
          Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
            (s := family) (t := support) (f := pick)
            pick_mem_support fiberLarge
        let throughPoint := family.filter fun set => point ∈ set
        have throughPointLarge : priorBound < throughPoint.card := by
          apply pointFiber.trans_le
          apply Finset.card_le_card
          intro set present
          rw [Finset.mem_filter] at present ⊢
          refine ⟨present.1, ?_⟩
          have picked := pick_mem_set set present.1
          rw [present.2] at picked
          exact picked
        let erased := throughPoint.image fun set => set.erase point
        have eraseInjective : Set.InjOn (fun set : Finset α => set.erase point)
            ↑throughPoint := by
          intro left leftPresent right rightPresent equal
          change left ∈ throughPoint at leftPresent
          change right ∈ throughPoint at rightPresent
          rw [Finset.mem_filter] at leftPresent rightPresent
          calc
            left = insert point (left.erase point) :=
              (Finset.insert_erase leftPresent.2).symm
            _ = insert point (right.erase point) := congrArg (insert point) equal
            _ = right := Finset.insert_erase rightPresent.2
        have erasedCard : erased.card = throughPoint.card := by
          exact Finset.card_image_iff.mpr eraseInjective
        have erasedUniform : ∀ set ∈ erased, set.card = width := by
          intro set present
          rw [Finset.mem_image] at present
          obtain ⟨original, originalPresent, rfl⟩ := present
          rw [Finset.mem_filter] at originalPresent
          rw [Finset.card_erase_of_mem originalPresent.2,
            uniform original originalPresent.1]
          omega
        have erasedLarge : priorBound < erased.card := by
          rw [erasedCard]
          exact throughPointLarge
        obtain ⟨smallPetals, smallSubset, smallCard, core, smallSunflower⟩ :=
          inductionHypothesis erased erasedUniform erasedLarge
        let lifted := smallPetals.image fun set => insert point set
        have pointNotMemErased : ∀ set ∈ erased, point ∉ set := by
          intro set present
          rw [Finset.mem_image] at present
          obtain ⟨original, _, rfl⟩ := present
          simp
        have insertInjective : Set.InjOn (fun set : Finset α => insert point set)
            ↑smallPetals := by
          intro left leftPresent right rightPresent equal
          have leftNoPoint := pointNotMemErased left (smallSubset leftPresent)
          have rightNoPoint := pointNotMemErased right (smallSubset rightPresent)
          calc
            left = (insert point left).erase point := by simp [leftNoPoint]
            _ = (insert point right).erase point :=
              congrArg (fun set : Finset α => set.erase point) equal
            _ = right := by simp [rightNoPoint]
        have liftedCard : lifted.card = petals := by
          change (smallPetals.image fun set => insert point set).card = petals
          rw [Finset.card_image_iff.mpr insertInjective, smallCard]
        have liftedSubset : lifted ⊆ family := by
          intro set present
          change set ∈ smallPetals.image (fun set => insert point set) at present
          rw [Finset.mem_image] at present
          obtain ⟨small, smallPresent, rfl⟩ := present
          have erasedPresent := smallSubset smallPresent
          change small ∈ throughPoint.image (fun set => set.erase point) at erasedPresent
          rw [Finset.mem_image] at erasedPresent
          obtain ⟨original, originalPresent, erasedEqual⟩ := erasedPresent
          rw [Finset.mem_filter] at originalPresent
          have setEqual : insert point small = original := by
            calc
              insert point small = insert point (original.erase point) := by
                rw [erasedEqual]
              _ = original := Finset.insert_erase originalPresent.2
          rw [setEqual]
          exact originalPresent.1
        refine ⟨lifted, liftedSubset, liftedCard, insert point core, ?_⟩
        intro left leftPresent right rightPresent different
        change left ∈ smallPetals.image (fun set => insert point set) at leftPresent
        change right ∈ smallPetals.image (fun set => insert point set) at rightPresent
        rw [Finset.mem_image] at leftPresent rightPresent
        obtain ⟨leftSmall, leftSmallPresent, rfl⟩ := leftPresent
        obtain ⟨rightSmall, rightSmallPresent, rfl⟩ := rightPresent
        have smallDifferent : leftSmall ≠ rightSmall := by
          intro equal
          apply different
          rw [equal]
        have intersection := smallSunflower leftSmallPresent rightSmallPresent
          smallDifferent
        rw [← Finset.insert_inter_distrib, intersection]

/-- The size bound used for families of sets of size at most `width`.  The
extra `width + 1` partitions the family into uniform layers. -/
def bound (petals width : Nat) : Nat :=
  (width + 1) * ((petals - 1) ^ width * width.factorial)

/-- The elementary sunflower lemma for bounded-size set families. -/
theorem containsSunflower_of_bounded
    [DecidableEq α]
    (petals : Nat)
    (two_le : 2 ≤ petals)
    (width : Nat)
    (family : Finset (Finset α))
    (bounded : ∀ set ∈ family, set.card ≤ width)
    (large : bound petals width < family.card) :
    ContainsSunflower petals family := by
  classical
  let uniformBound := (petals - 1) ^ width * width.factorial
  have mapsTo : ∀ set ∈ family,
      set.card ∈ Finset.range (width + 1) := by
    intro set present
    rw [Finset.mem_range]
    have := bounded set present
    omega
  have averageLarge :
      (Finset.range (width + 1)).card * uniformBound < family.card := by
    simpa [bound, uniformBound] using large
  obtain ⟨layerSize, layerSizePresent, layerLarge⟩ :=
    Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
      (s := family) (t := Finset.range (width + 1))
      (f := Finset.card) mapsTo averageLarge
  have layerSizeLe : layerSize ≤ width := by
    rw [Finset.mem_range] at layerSizePresent
    omega
  let layer := family.filter fun set => set.card = layerSize
  have layerLarge' : uniformBound < layer.card := by
    exact layerLarge
  have layerUniform : ∀ set ∈ layer, set.card = layerSize := by
    intro set present
    exact (Finset.mem_filter.mp present).2
  have layerThresholdLe :
      (petals - 1) ^ layerSize * layerSize.factorial ≤ uniformBound := by
    apply Nat.mul_le_mul
    · exact Nat.pow_le_pow_right (by omega) layerSizeLe
    · exact Nat.factorial_le layerSizeLe
  have layerThresholdLarge :
      (petals - 1) ^ layerSize * layerSize.factorial < layer.card :=
    layerThresholdLe.trans_lt layerLarge'
  obtain ⟨selected, selectedSubset, selectedCard, core, sunflower⟩ :=
    containsSunflower_of_uniform petals two_le layerSize layer
      layerUniform layerThresholdLarge
  refine ⟨selected, selectedSubset.trans ?_, selectedCard, core, sunflower⟩
  exact Finset.filter_subset _ _

end

end Sunflower
end Algebraic
