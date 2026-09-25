/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Fusion.Semifilter

/-!
# Generated semi-filter closure

Given a point and a list of fusion pairs, start with the full complement and
the restricted generators true at the point, then close upward and apply every
pair rule `(left, right) ↦ left ∩ right`.  This is the least semi-filter-like
family forced by the generators and the pair rules.

The empty set is derivable at exactly the target points when the pair list is
a cover of all semi-filters.  Outside the target, the corresponding complement
point belongs to every derivable set.  This closure characterization is the
combinatorial kernel of the cover-to-cyclic direction of fusion completeness.
-/

@[expose] public section

namespace Algebraic
namespace Fusion

variable {Γ : Type*}

/-- Sets forced into the semi-filter generated above `point` by a list of
fusion pairs. -/
inductive PairDerivation
    (problem : SetProblem Γ)
    (pairs : List (Pair problem))
    (point : Γ) : Set (Problem.Outside problem) → Prop
  /-- Every semi-filter contains the full set. -/
  | univ : PairDerivation problem pairs point Set.univ
  /-- Restricted generators true at the reference point are forced. -/
  | generator (input : Fin problem.inputCount)
      (present : point ∈ problem.inputs input) :
      PairDerivation problem pairs point
        (problem.restrict (problem.inputs input))
  /-- Forced membership is upward closed. -/
  | upward {lower upper : Set (Problem.Outside problem)}
      (derived : PairDerivation problem pairs point lower)
      (subset : lower ⊆ upper) :
      PairDerivation problem pairs point upper
  /-- Every listed fusion pair contributes its intersection rule. -/
  | fusion (pair : Pair problem)
      (present : pair ∈ pairs)
      (leftDerived : PairDerivation problem pairs point pair.1)
      (rightDerived : PairDerivation problem pairs point pair.2) :
      PairDerivation problem pairs point (pair.1 ∩ pair.2)

variable {problem : SetProblem Γ}
variable {pairs : List (Pair problem)}
variable {point : Γ}

/-- If the generated closure avoids the empty set, it is a genuine
semi-filter. -/
def PairDerivation.semifilter
    (empty_not_derived : ¬ PairDerivation problem pairs point ∅) :
    Semifilter (Problem.Outside problem) where
  carrier := { set | PairDerivation problem pairs point set }
  nonempty := ⟨Set.univ, .univ⟩
  upward := by
    intro lower upper derived subset
    exact .upward derived subset
  empty_not_mem := empty_not_derived

@[simp] theorem PairDerivation.mem_semifilter
    (empty_not_derived : ¬ PairDerivation problem pairs point ∅)
    (set : Set (Problem.Outside problem)) :
    set ∈ PairDerivation.semifilter empty_not_derived ↔
      PairDerivation problem pairs point set := Iff.rfl

/-- The generated semi-filter is above its reference point. -/
theorem PairDerivation.semifilter_above
    (empty_not_derived : ¬ PairDerivation problem pairs point ∅) :
    (PairDerivation.semifilter empty_not_derived).Above
      (problem := problem) point := by
  intro input present
  exact .generator input present

/-- The generated semi-filter preserves every pair used to generate it. -/
theorem PairDerivation.semifilter_preservesPair
    (empty_not_derived : ¬ PairDerivation problem pairs point ∅)
    (pair : Pair problem)
    (present : pair ∈ pairs) :
    (PairDerivation.semifilter empty_not_derived).PreservesPair pair := by
  intro leftDerived rightDerived
  exact .fusion pair present leftDerived rightDerived

/-- A cover forces the empty set into the generated closure at every target
point. -/
theorem PairCover.derives_empty
    (cover : PairCover problem SemifilterClass.all)
    (point : Γ)
    (pointMem : point ∈ problem.target) :
    PairDerivation problem cover.pairs point ∅ := by
  by_contra empty_not_derived
  let filter := PairDerivation.semifilter empty_not_derived
  apply cover.isCover point pointMem filter trivial
    (PairDerivation.semifilter_above empty_not_derived)
  intro pair present
  exact PairDerivation.semifilter_preservesPair
    empty_not_derived pair present

/-- An outside point belongs to every set derivable above its ambient value. -/
theorem PairDerivation.counterexample_mem
    (counterexample : Problem.Outside problem)
    {set : Set (Problem.Outside problem)}
    (derived : PairDerivation problem pairs counterexample.1 set) :
    counterexample ∈ set := by
  induction derived with
  | univ => simp
  | generator input present =>
      rw [Problem.mem_restrict]
      exact present
  | upward derived subset inductionHypothesis =>
      exact subset inductionHypothesis
  | fusion pair present leftDerived rightDerived
      leftInduction rightInduction =>
      exact ⟨leftInduction, rightInduction⟩

/-- The empty set can never be derived at a point outside the target. -/
theorem PairDerivation.empty_not_of_outside
    (counterexample : Problem.Outside problem) :
    ¬ PairDerivation problem pairs counterexample.1 ∅ := by
  intro derived
  exact (PairDerivation.counterexample_mem counterexample derived)

/-- For a pair cover, generated closure derives the empty set exactly on the
target. -/
theorem PairCover.derives_empty_iff
    (cover : PairCover problem SemifilterClass.all)
    (point : Γ) :
    PairDerivation problem cover.pairs point ∅ ↔
      point ∈ problem.target := by
  constructor
  · intro derived
    by_contra outside
    exact PairDerivation.empty_not_of_outside
      (counterexample := ⟨point, outside⟩) derived
  · exact cover.derives_empty point

/-- A proposed state for all subset-indexed closure gates is pre-fixed when it
contains the full-set seed, the generators, upward propagation, and every
fusion rule. -/
structure PairClosure.IsPrefixed
    (problem : SetProblem Γ)
    (pairs : List (Pair problem))
    (state : Set (Problem.Outside problem) → Set Γ) : Prop where
  /-- The full complement is forced at every reference point. -/
  univ : Set.univ ⊆ state Set.univ
  /-- Each generator feeds its corresponding restricted-set gate. -/
  generator : ∀ input,
    problem.inputs input ⊆
      state (problem.restrict (problem.inputs input))
  /-- Subset-indexed gates propagate upward. -/
  upward : ∀ {lower upper}, lower ⊆ upper →
    state lower ⊆ state upper
  /-- Each fusion pair contributes one intersection rule. -/
  fusion : ∀ pair ∈ pairs,
    state pair.1 ∩ state pair.2 ⊆ state (pair.1 ∩ pair.2)

/-- State generated by the inductive pair closure. -/
def PairClosure.generatedState
    (problem : SetProblem Γ)
    (pairs : List (Pair problem)) :
    Set (Problem.Outside problem) → Set Γ :=
  fun set => { point | PairDerivation problem pairs point set }

/-- The generated state is closed under all pair-closure rules. -/
theorem PairClosure.generatedState_prefixed
    (problem : SetProblem Γ)
    (pairs : List (Pair problem)) :
    PairClosure.IsPrefixed problem pairs
      (PairClosure.generatedState problem pairs) where
  univ := by
    intro point _
    exact .univ
  generator := by
    intro input point present
    exact .generator input present
  upward := by
    intro lower upper subset point derived
    exact .upward derived subset
  fusion := by
    intro pair pairPresent point derived
    exact .fusion pair pairPresent derived.1 derived.2

/-- Inductive pair closure is the least state closed under the four forcing
rules. -/
theorem PairClosure.generatedState_least
    (problem : SetProblem Γ)
    (pairs : List (Pair problem))
    (state : Set (Problem.Outside problem) → Set Γ)
    (prefixed : PairClosure.IsPrefixed problem pairs state) :
    ∀ set, PairClosure.generatedState problem pairs set ⊆ state set := by
  intro set point derived
  induction derived with
  | univ => exact prefixed.univ (Set.mem_univ point)
  | generator input present => exact prefixed.generator input present
  | upward derived subset inductionHypothesis =>
      exact prefixed.upward subset inductionHypothesis
  | fusion pair pairPresent leftDerived rightDerived
      leftInduction rightInduction =>
      exact prefixed.fusion pair pairPresent
        ⟨leftInduction, rightInduction⟩

/-- The empty-index gate of the generated closure state is exactly the target
set when the pairs form a cover. -/
theorem PairCover.generatedState_empty
    (cover : PairCover problem SemifilterClass.all) :
    PairClosure.generatedState problem cover.pairs ∅ = problem.target := by
  ext point
  exact cover.derives_empty_iff point

end Fusion
end Algebraic
