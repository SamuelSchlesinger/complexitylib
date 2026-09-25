/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.Combinatorics.Sunflower
public import Complexitylib.Algebraic.LowerBound.Monotone.Clique.Basic

/-!
# Sunflower plucking for clique approximators

A bounded-width clique approximator is a finite family of vertex sets.  A
sunflower pluck removes all petals and inserts their common core.  This can
only enlarge the accepted graph set, and it strictly decreases the number of
terms when there are at least two petals.

Repeated plucking therefore terminates.  The resulting normal form has at
most `Sunflower.bound petals width` terms, and the number of plucks is at most
the cardinality of the starting family.
-/

@[expose] public section

namespace Algebraic
namespace Monotone
namespace Clique
namespace Plucking

noncomputable section

/-- A finite family of finite vertex sets. -/
abbrev Family (n : Nat) := Finset (Finset (Fin n))

/-- A family is a bounded-width clique DNF. -/
def Bounded (width : Nat) (family : Family n) : Prop :=
  ∀ set ∈ family, set.card ≤ width

/-- One sunflower replacement. -/
structure Step
    (petalCount : Nat)
    (before after : Family n) where
  /-- The sunflower terms removed by this step. -/
  petals : Family n
  /-- The common core inserted by this step. -/
  core : Finset (Fin n)
  /-- Every removed petal belonged to the starting family. -/
  petals_subset : petals ⊆ before
  /-- The selected sunflower has the requested number of petals. -/
  petals_card : petals.card = petalCount
  /-- Distinct selected petals have exactly the recorded core in common. -/
  sunflower : Sunflower.IsSunflowerWithCore petals core
  /-- The result removes all petals and inserts their core. -/
  result : after = insert core (before \ petals)

/-- A sunflower core lies in each petal when there are at least two petals. -/
theorem core_subset_of_sunflower
    {petalCount : Nat}
    (two_le : 2 ≤ petalCount)
    {petals : Family n}
    {core petal : Finset (Fin n)}
    (petalsCard : petals.card = petalCount)
    (sunflower : Sunflower.IsSunflowerWithCore petals core)
    (present : petal ∈ petals) :
    core ⊆ petal := by
  classical
  have one_lt : 1 < petals.card := by
    rw [petalsCard]
    exact two_le
  have erasedNonempty : (petals.erase petal).Nonempty := by
    rw [← Finset.card_pos, Finset.card_erase_of_mem present]
    omega
  obtain ⟨other, otherPresentErased⟩ := erasedNonempty
  have otherPresent : other ∈ petals :=
    Finset.mem_of_mem_erase otherPresentErased
  have different : petal ≠ other := by
    exact fun equal => (Finset.ne_of_mem_erase otherPresentErased) equal.symm
  have intersection := sunflower present otherPresent different
  rw [← intersection]
  exact Finset.inter_subset_left

private theorem core_subset_petal
    {petalCount : Nat}
    (two_le : 2 ≤ petalCount)
    {before after : Family n}
    (step : Step petalCount before after)
    {petal : Finset (Fin n)}
    (present : petal ∈ step.petals) :
    step.core ⊆ petal :=
  core_subset_of_sunflower two_le step.petals_card step.sunflower present

/-- One pluck strictly reduces family cardinality. -/
theorem Step.card_lt
    {petalCount : Nat}
    (two_le : 2 ≤ petalCount)
    {before after : Family n}
    (step : Step petalCount before after) :
    after.card < before.card := by
  classical
  have petalCountLe : petalCount ≤ before.card := by
    rw [← step.petals_card]
    exact Finset.card_le_card step.petals_subset
  calc
    after.card = (insert step.core (before \ step.petals)).card :=
      congrArg Finset.card step.result
    _ ≤ (before \ step.petals).card + 1 := Finset.card_insert_le _ _
    _ = (before.card - petalCount) + 1 := by
      rw [Finset.card_sdiff_of_subset step.petals_subset, step.petals_card]
    _ < before.card := by omega

/-- Bounded width is preserved by one pluck. -/
theorem Step.bounded
    {petalCount : Nat}
    (two_le : 2 ≤ petalCount)
    {before after : Family n}
    (step : Step petalCount before after)
    {width : Nat}
    (bounded : Bounded width before) :
    Bounded width after := by
  classical
  intro set present
  rw [step.result, Finset.mem_insert] at present
  rcases present with equal | remaining
  · subst set
    have petalsNonempty : step.petals.Nonempty := by
      rw [← Finset.card_pos, step.petals_card]
      omega
    obtain ⟨petal, petalPresent⟩ := petalsNonempty
    exact Finset.card_le_card (core_subset_petal two_le step petalPresent) |>.trans
      (bounded petal (step.petals_subset petalPresent))
  · exact bounded set (Finset.mem_sdiff.mp remaining).1

/-- A pluck preserves every graph accepted by the starting family. -/
theorem Step.acceptance_mono
    {petalCount : Nat}
    (two_le : 2 ≤ petalCount)
    {before after : Family n}
    (step : Step petalCount before after)
    {assignment : Fin (edgeCount n) → Bool}
    (accepted : ∃ set ∈ before, Contains assignment set) :
    ∃ set ∈ after, Contains assignment set := by
  classical
  rcases step with ⟨petals, core, petalsSubset, petalsCard, sunflower, rfl⟩
  obtain ⟨set, setPresent, contains⟩ := accepted
  by_cases isPetal : set ∈ petals
  · refine ⟨core, Finset.mem_insert_self _ _,
      Contains.mono_vertices
        (core_subset_of_sunflower two_le petalsCard sunflower isPetal) contains⟩
  · refine ⟨set, ?_, contains⟩
    rw [Finset.mem_insert]
    exact Or.inr (Finset.mem_sdiff.mpr ⟨setPresent, isPetal⟩)

/-- A proof-relevant sequence of exactly `steps` plucks. -/
inductive Reduction (petalCount : Nat) : Nat → Family n → Family n → Prop
  | refl (family : Family n) : Reduction petalCount 0 family family
  | step {before middle after : Family n} {steps : Nat} :
      Step petalCount before middle →
      Reduction petalCount steps middle after →
      Reduction petalCount (steps + 1) before after

/-- A reduction has at most one step per starting term. -/
theorem Reduction.steps_le_card
    {petalCount : Nat}
    (two_le : 2 ≤ petalCount)
    {steps : Nat}
    {before after : Family n}
    (reduction : Reduction petalCount steps before after) :
    steps ≤ before.card := by
  induction reduction with
  | refl => simp
  | @step before middle after steps first rest inductionHypothesis =>
      have decreases := Step.card_lt two_le first
      omega

/-- Bounded width is preserved throughout a reduction. -/
theorem Reduction.bounded
    {petalCount : Nat}
    (two_le : 2 ≤ petalCount)
    {steps : Nat}
    {before after : Family n}
    (reduction : Reduction petalCount steps before after)
    {width : Nat}
    (bounded : Bounded width before) :
    Bounded width after := by
  induction reduction with
  | refl => exact bounded
  | step first rest inductionHypothesis =>
      exact inductionHypothesis (first.bounded two_le bounded)

/-- Acceptance is monotone throughout a reduction. -/
theorem Reduction.acceptance_mono
    {petalCount : Nat}
    (two_le : 2 ≤ petalCount)
    {steps : Nat}
    {before after : Family n}
    (reduction : Reduction petalCount steps before after)
    {assignment : Fin (edgeCount n) → Bool}
    (accepted : ∃ set ∈ before, Contains assignment set) :
    ∃ set ∈ after, Contains assignment set := by
  induction reduction with
  | refl => exact accepted
  | step first rest inductionHypothesis =>
      exact inductionHypothesis (first.acceptance_mono two_le accepted)

/-- Every finite family reduces to a sunflower-free family. -/
theorem exists_terminal
    (petalCount : Nat)
    (two_le : 2 ≤ petalCount)
    (family : Family n) :
    ∃ steps terminal,
      Reduction petalCount steps family terminal ∧
      ¬ Sunflower.ContainsSunflower petalCount terminal := by
  classical
  induction family using (measure Finset.card).wf.induction with
  | h family inductionHypothesis =>
      by_cases found : Sunflower.ContainsSunflower petalCount family
      · obtain ⟨petals, petalsSubset, petalsCard, core, sunflower⟩ := found
        let next := insert core (family \ petals)
        let first : Step petalCount family next :=
          { petals := petals
            core := core
            petals_subset := petalsSubset
            petals_card := petalsCard
            sunflower := sunflower
            result := rfl }
        have smaller : next.card < family.card := first.card_lt two_le
        obtain ⟨steps, terminal, rest, terminalFree⟩ :=
          inductionHypothesis next smaller
        exact ⟨steps + 1, terminal, Reduction.step first rest, terminalFree⟩
      · exact ⟨0, family, Reduction.refl family, found⟩

/-- A chosen terminal sunflower-free normal form. -/
def normalize
    (petalCount : Nat)
    (two_le : 2 ≤ petalCount)
    (family : Family n) : Family n :=
  Classical.choose
    (Classical.choose_spec (exists_terminal petalCount two_le family))

/-- Number of plucks in the chosen normalization. -/
def normalizeSteps
    (petalCount : Nat)
    (two_le : 2 ≤ petalCount)
    (family : Family n) : Nat :=
  Classical.choose (exists_terminal petalCount two_le family)

/-- The chosen normal form comes with a reduction certificate. -/
theorem reduction_normalize
    (petalCount : Nat)
    (two_le : 2 ≤ petalCount)
    (family : Family n) :
    Reduction petalCount (normalizeSteps petalCount two_le family) family
      (normalize petalCount two_le family) :=
  (Classical.choose_spec
    (Classical.choose_spec (exists_terminal petalCount two_le family))).1

/-- The chosen normal form is sunflower-free. -/
theorem normalize_sunflowerFree
    (petalCount : Nat)
    (two_le : 2 ≤ petalCount)
    (family : Family n) :
    ¬ Sunflower.ContainsSunflower petalCount
      (normalize petalCount two_le family) :=
  (Classical.choose_spec
    (Classical.choose_spec (exists_terminal petalCount two_le family))).2

/-- Normalization uses at most one pluck per starting term. -/
theorem normalizeSteps_le_card
    (petalCount : Nat)
    (two_le : 2 ≤ petalCount)
    (family : Family n) :
    normalizeSteps petalCount two_le family ≤ family.card :=
  (reduction_normalize petalCount two_le family).steps_le_card two_le

/-- Normalization preserves bounded width. -/
theorem normalize_bounded
    (petalCount : Nat)
    (two_le : 2 ≤ petalCount)
    (family : Family n)
    {width : Nat}
    (bounded : Bounded width family) :
    Bounded width (normalize petalCount two_le family) :=
  (reduction_normalize petalCount two_le family).bounded two_le bounded

/-- A bounded normal form has at most the elementary sunflower bound many
terms. -/
theorem normalize_card_le
    (petalCount : Nat)
    (two_le : 2 ≤ petalCount)
    (family : Family n)
    {width : Nat}
    (bounded : Bounded width family) :
    (normalize petalCount two_le family).card ≤
      Sunflower.bound petalCount width := by
  by_contra tooLarge
  have contains := Sunflower.containsSunflower_of_bounded petalCount two_le
    width (normalize petalCount two_le family)
      (normalize_bounded petalCount two_le family bounded)
      (Nat.lt_of_not_ge tooLarge)
  exact normalize_sunflowerFree petalCount two_le family contains

/-- Normalization preserves acceptance. -/
theorem normalize_acceptance_mono
    (petalCount : Nat)
    (two_le : 2 ≤ petalCount)
    (family : Family n)
    {assignment : Fin (edgeCount n) → Bool}
    (accepted : ∃ set ∈ family, Contains assignment set) :
    ∃ set ∈ normalize petalCount two_le family,
      Contains assignment set :=
  (reduction_normalize petalCount two_le family).acceptance_mono two_le accepted

end

end Plucking
end Clique
end Monotone
end Algebraic
