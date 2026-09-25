/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.Basis.AndOr
public import Complexitylib.Algebraic.LowerBound.Fusion.Framework

/-!
# Set-theoretic fusion with semi-filters

This file instantiates the algebra-generic fusion engine with the classical
set-theoretic framework.  A construction problem consists of generator subsets
of an ambient type and a target subset.  Witnesses are target points equipped
with semi-filters over the complement of the target.

The public combinatorial objects are lists of pairs of subsets.  Such a list is
a cover when no admissible semi-filter above a target point preserves every
pair.  Every AND/OR circuit constructing the target yields a cover whose length
is exactly its number of AND gates.
-/

@[expose] public section

namespace Algebraic
namespace Fusion

/-- A nontrivial upward-closed family of subsets. -/
structure Semifilter (U : Type u) where
  /-- Subsets accepted by the semi-filter. -/
  carrier : Set (Set U)
  /-- At least one subset is accepted. -/
  nonempty : carrier.Nonempty
  /-- Acceptance is upward closed. -/
  upward : ∀ {lower upper : Set U},
    lower ∈ carrier → lower ⊆ upper → upper ∈ carrier
  /-- The empty set is not accepted. -/
  empty_not_mem : ∅ ∉ carrier

instance : SetLike (Semifilter U) (Set U) where
  coe := Semifilter.carrier
  coe_injective := by
    intro left right equal
    cases left
    cases right
    cases equal
    rfl

@[ext] theorem Semifilter.ext
    {left right : Semifilter U}
    (equal : ∀ set, set ∈ left ↔ set ∈ right) :
    left = right := by
  apply SetLike.coe_injective
  ext set
  exact equal set

/-- Every semi-filter contains the full set. -/
theorem Semifilter.univ_mem (filter : Semifilter U) :
    Set.univ ∈ filter := by
  obtain ⟨set, present⟩ := filter.nonempty
  exact filter.upward present (Set.subset_univ set)

/-- Acceptance of a set implies acceptance after union on the right. -/
theorem Semifilter.union_right
    (filter : Semifilter U)
    {left : Set U}
    (right : Set U)
    (present : left ∈ filter) :
    left ∪ right ∈ filter :=
  filter.upward present Set.subset_union_left

/-- Acceptance of a set implies acceptance after union on the left. -/
theorem Semifilter.union_left
    (filter : Semifilter U)
    (left : Set U)
    {right : Set U}
    (present : right ∈ filter) :
    left ∪ right ∈ filter :=
  filter.upward present Set.subset_union_right

/-- A set-valued fusion problem is a discrete construction problem. -/
abbrev SetProblem (Γ : Type u) := Problem (Set Γ)

/-- The complement of a set problem's target, as an ambient subtype. -/
abbrev Problem.Outside (problem : SetProblem Γ) :=
  { point : Γ // point ∉ problem.target }

/-- Restrict a subset of the ambient type to the target complement. -/
def Problem.restrict
    (problem : SetProblem Γ)
    (set : Set Γ) : Set (Problem.Outside problem) :=
  Subtype.val ⁻¹' set

@[simp] theorem Problem.mem_restrict
    (problem : SetProblem Γ)
    (set : Set Γ)
    (point : Problem.Outside problem) :
    point ∈ problem.restrict set ↔ point.1 ∈ set := Iff.rfl

@[simp] theorem Problem.restrict_empty
    (problem : SetProblem Γ) :
    problem.restrict ∅ = ∅ := rfl

@[simp] theorem Problem.restrict_union
    (problem : SetProblem Γ)
    (left right : Set Γ) :
    problem.restrict (left ∪ right) =
      problem.restrict left ∪ problem.restrict right := rfl

@[simp] theorem Problem.restrict_inter
    (problem : SetProblem Γ)
    (left right : Set Γ) :
    problem.restrict (left ∩ right) =
      problem.restrict left ∩ problem.restrict right := rfl

@[simp] theorem Problem.restrict_target
    (problem : SetProblem Γ) :
    problem.restrict problem.target = ∅ := by
  ext point
  simp [Problem.restrict, point.property]

/-- A semi-filter is above a point when it accepts every generator containing it. -/
def Semifilter.Above
    {problem : SetProblem Γ}
    (filter : Semifilter (Problem.Outside problem))
    (point : Γ) : Prop :=
  ∀ input, point ∈ problem.inputs input →
    problem.restrict (problem.inputs input) ∈ filter

/-- A selectable class of semi-filters for variants of cover complexity. -/
abbrev SemifilterClass (problem : SetProblem Γ) :=
  Semifilter (Problem.Outside problem) → Prop

/-- The unrestricted class of all semi-filters. -/
def SemifilterClass.all (_ : Semifilter (Problem.Outside problem)) : Prop := True

/-- A semi-ultrafilter accepts either a set or its complement.  Unlike an
ultrafilter, it is not required to be closed under intersections. -/
def Semifilter.IsUltra
    (filter : Semifilter U) : Prop :=
  ∀ set : Set U, set ∈ filter ∨ setᶜ ∈ filter

/-- The selectable class of all semi-ultrafilters. -/
def SemifilterClass.ultra
    (filter : Semifilter (Problem.Outside problem)) : Prop :=
  filter.IsUltra

/-- A target point and an admissible semi-filter above that point. -/
structure SemifilterWitness
    (problem : SetProblem Γ)
    (admissible : SemifilterClass problem) where
  /-- Point of the target set being fused. -/
  point : Γ
  /-- The distinguished point belongs to the target. -/
  point_mem : point ∈ problem.target
  /-- Semi-filter over the target complement. -/
  filter : Semifilter (Problem.Outside problem)
  /-- This semi-filter belongs to the selected witness class. -/
  admissible_filter : admissible filter
  /-- This semi-filter lies above the distinguished target point. -/
  above : filter.Above point

/-- The standard semi-filter observation model for set-theoretic fusion. -/
def semifilterModel
    (problem : SetProblem Γ)
    (admissible : SemifilterClass problem := SemifilterClass.all) :
    Model AndOr.andCost (AndOr.setInterpretation Γ) problem where
  Witness := SemifilterWitness problem admissible
  reference witness set := witness.point ∈ set
  observed witness set := problem.restrict set ∈ witness.filter
  input_sound := by
    intro witness input present
    exact witness.above input present
  target_reference := fun witness => witness.point_mem
  target_not_observed := by
    intro witness
    change problem.restrict problem.target ∉ witness.filter.carrier
    rw [Problem.restrict_target]
    exact witness.filter.empty_not_mem

/-- A local fusion pair consists of two subsets of the target complement. -/
abbrev Pair (problem : SetProblem Γ) :=
  Set (Problem.Outside problem) × Set (Problem.Outside problem)

/-- A semi-filter preserves a pair when it accepts their intersection whenever
it accepts both members. -/
def Semifilter.PreservesPair
    (filter : Semifilter U)
    (pair : Set U × Set U) : Prop :=
  pair.1 ∈ filter → pair.2 ∈ filter → pair.1 ∩ pair.2 ∈ filter

/-- A list of pairs covers every admissible semi-filter above a target point. -/
def Problem.IsPairCover
    (problem : SetProblem Γ)
    (admissible : SemifilterClass problem)
    (pairs : List (Pair problem)) : Prop :=
  ∀ point, point ∈ problem.target →
    ∀ filter : Semifilter (Problem.Outside problem),
      admissible filter → filter.Above point →
        ¬ ∀ pair ∈ pairs, filter.PreservesPair pair

/-- A proof-carrying set-theoretic fusion cover. -/
structure PairCover
    (problem : SetProblem Γ)
    (admissible : SemifilterClass problem := SemifilterClass.all) where
  /-- Pairs of subsets in the cover. -/
  pairs : List (Pair problem)
  /-- No admissible semi-filter above the target preserves every pair. -/
  isCover : problem.IsPairCover admissible pairs

/-- The number of pairs in a set-theoretic fusion cover. -/
def PairCover.cost
    (cover : PairCover problem admissible) : Nat :=
  cover.pairs.length

/-- Classical set-theoretic cover complexity `ρ`. -/
noncomputable def pairCoverComplexity
    (problem : SetProblem Γ)
    (admissible : SemifilterClass problem := SemifilterClass.all) : ℕ∞ :=
  ⨅ cover : PairCover problem admissible, (cover.cost : ℕ∞)

/-- Every concrete pair cover upper-bounds pair-cover complexity. -/
theorem pairCoverComplexity_le
    (problem : SetProblem Γ)
    (admissible : SemifilterClass problem)
    (cover : PairCover problem admissible) :
    pairCoverComplexity problem admissible ≤ cover.cost := by
  unfold pairCoverComplexity
  exact iInf_le _ cover

/-- The pair contributed by an AND atom; OR atoms contribute no pair. -/
def Atom.andPair?
    (problem : SetProblem Γ)
    (atom : Atom AndOr.signature (Set Γ)) : Option (Pair problem) :=
  match atom with
  | ⟨.and, arguments⟩ => some
      (problem.restrict (arguments ⟨0, by decide⟩),
        problem.restrict (arguments ⟨1, by decide⟩))
  | ⟨.or, _⟩ => none

@[simp] theorem Atom.andPair?_and
    (problem : SetProblem Γ)
    (arguments : Fin (AndOr.signature.Arity .and) → Set Γ) :
    Atom.andPair? problem (⟨.and, arguments⟩ :
      Atom AndOr.signature (Set Γ)) =
      some (problem.restrict (arguments ⟨0, by decide⟩),
        problem.restrict (arguments ⟨1, by decide⟩)) := rfl

@[simp] theorem Atom.andPair?_or
    (problem : SetProblem Γ)
    (arguments : Fin (AndOr.signature.Arity .or) → Set Γ) :
    Atom.andPair? problem (⟨.or, arguments⟩ :
      Atom AndOr.signature (Set Γ)) = none := rfl

/-- Keep the intersection pairs from a list of AND/OR atoms. -/
def intersectionPairs
    (problem : SetProblem Γ)
    (atoms : List (Atom AndOr.signature (Set Γ))) : List (Pair problem) :=
  atoms.filterMap (Atom.andPair? problem)

@[simp] theorem intersectionPairs_cons_and
    (problem : SetProblem Γ)
    (arguments : Fin (AndOr.signature.Arity .and) → Set Γ)
    (atoms : List (Atom AndOr.signature (Set Γ))) :
    intersectionPairs problem (⟨.and, arguments⟩ :: atoms) =
      (problem.restrict (arguments ⟨0, by decide⟩),
        problem.restrict (arguments ⟨1, by decide⟩)) ::
          intersectionPairs problem atoms := by
  unfold intersectionPairs
  rw [List.filterMap_cons_some (Atom.andPair?_and problem arguments)]

@[simp] theorem intersectionPairs_cons_or
    (problem : SetProblem Γ)
    (arguments : Fin (AndOr.signature.Arity .or) → Set Γ)
    (atoms : List (Atom AndOr.signature (Set Γ))) :
    intersectionPairs problem (⟨.or, arguments⟩ :: atoms) =
      intersectionPairs problem atoms := by
  unfold intersectionPairs
  rw [List.filterMap_cons_none (Atom.andPair?_or problem arguments)]

/-- The number of extracted pairs is exactly the AND weight of the atoms. -/
theorem intersectionPairs_length
    (problem : SetProblem Γ)
    (atoms : List (Atom AndOr.signature (Set Γ))) :
    (intersectionPairs problem atoms).length =
      Atom.listCost atoms AndOr.andCost := by
  induction atoms with
  | nil => rfl
  | cons atom atoms inductionHypothesis =>
      cases atom with
      | mk op arguments =>
          cases op with
          | and =>
              simp [Atom.listCost, Atom.cost, inductionHypothesis,
                AndOr.andCost, Nat.add_comm]
          | or =>
              simp [Atom.listCost, Atom.cost, inductionHypothesis,
                AndOr.andCost]

/-- Semi-filters automatically preserve union atoms; preservation of the
associated pair is sufficient for an intersection atom. -/
theorem Atom.preservedBy_semifilterModel
    (problem : SetProblem Γ)
    (admissible : SemifilterClass problem)
    (atom : Atom AndOr.signature (Set Γ))
    (witness : SemifilterWitness problem admissible)
    (pairPreserved : ∀ pair,
      atom.andPair? problem = some pair →
        witness.filter.PreservesPair pair) :
    atom.PreservedBy (semifilterModel problem admissible) witness := by
  cases atom with
  | mk op arguments =>
      cases op with
      | and =>
          simp only [Atom.PreservedBy, Model.Sound, Atom.result,
            semifilterModel, AndOr.setInterpretation,
            Problem.restrict_inter, Set.mem_inter_iff] at *
          intro argumentsSound referenceResult
          have leftReference : witness.point ∈
              arguments ⟨0, by decide⟩ :=
            referenceResult.1
          have rightReference : witness.point ∈
              arguments ⟨1, by decide⟩ :=
            referenceResult.2
          have leftObserved :=
            argumentsSound ⟨0, by decide⟩ leftReference
          have rightObserved :=
            argumentsSound ⟨1, by decide⟩ rightReference
          have preserved := pairPreserved _ rfl leftObserved rightObserved
          exact preserved
      | or =>
          simp only [Atom.PreservedBy, Model.Sound, Atom.result,
            semifilterModel, AndOr.setInterpretation,
            Problem.restrict_union, Set.mem_union] at *
          intro argumentsSound referenceResult
          rcases referenceResult with leftReference | rightReference
          · exact witness.filter.union_right _
              (argumentsSound ⟨0, by decide⟩ leftReference)
          · exact witness.filter.union_left _
              (argumentsSound ⟨1, by decide⟩ rightReference)

/-- Every constructing AND/OR circuit yields its classical semi-filter cover. -/
def pairCoverOfCircuit
    (problem : SetProblem Γ)
    (admissible : SemifilterClass problem)
    (circuit : Circuit AndOr.signature problem.inputCount g 1)
    (constructs : problem.Constructs circuit (AndOr.setInterpretation Γ)) :
    PairCover problem admissible where
  pairs := intersectionPairs problem
    (circuitAtoms circuit (AndOr.setInterpretation Γ) problem.inputs)
  isCover := by
    intro point pointMem filter filterAdmissible above preservesPairs
    let witness : SemifilterWitness problem admissible :=
      { point := point
        point_mem := pointMem
        filter := filter
        admissible_filter := filterAdmissible
        above := above }
    let genericCover := coverOfCircuit (semifilterModel problem admissible)
      circuit constructs
    apply genericCover.isCover witness
    intro atom atomMem
    apply atom.preservedBy_semifilterModel problem admissible witness
    intro pair equal
    apply preservesPairs pair
    change atom ∈ circuitAtoms circuit (AndOr.setInterpretation Γ)
      problem.inputs at atomMem
    simp only [intersectionPairs, List.mem_filterMap]
    exact ⟨atom, atomMem, equal⟩

/-- The extracted pair cover has exactly the circuit's number of AND gates. -/
theorem pairCoverOfCircuit_cost
    (problem : SetProblem Γ)
    (admissible : SemifilterClass problem)
    (circuit : Circuit AndOr.signature problem.inputCount g 1)
    (constructs : problem.Constructs circuit (AndOr.setInterpretation Γ)) :
    (pairCoverOfCircuit problem admissible circuit constructs).cost =
      circuit.cost AndOr.andCost := by
  rw [PairCover.cost, pairCoverOfCircuit, intersectionPairs_length]
  exact circuitAtoms_cost circuit (AndOr.setInterpretation Γ)
    problem.inputs AndOr.andCost

/-- A lower bound for all semi-filter pair covers is an AND-circuit lower bound. -/
theorem pairCover_lowerBound
    (problem : SetProblem Γ)
    (admissible : SemifilterClass problem)
    (coverLowerBound : ∀ cover : PairCover problem admissible,
      L ≤ cover.cost)
    (circuit : Circuit AndOr.signature problem.inputCount g 1)
    (constructs : problem.Constructs circuit (AndOr.setInterpretation Γ)) :
    L ≤ circuit.cost AndOr.andCost := by
  rw [← pairCoverOfCircuit_cost problem admissible circuit constructs]
  exact coverLowerBound (pairCoverOfCircuit problem admissible circuit constructs)

/-- Set-theoretic cover complexity lower-bounds every AND/OR construction. -/
theorem pairCoverComplexity_le_cost
    (problem : SetProblem Γ)
    (admissible : SemifilterClass problem)
    (circuit : Circuit AndOr.signature problem.inputCount g 1)
    (constructs : problem.Constructs circuit (AndOr.setInterpretation Γ)) :
    pairCoverComplexity problem admissible ≤
      circuit.cost AndOr.andCost := by
  calc
    pairCoverComplexity problem admissible ≤
        (pairCoverOfCircuit problem admissible circuit constructs).cost :=
      pairCoverComplexity_le problem admissible
        (pairCoverOfCircuit problem admissible circuit constructs)
    _ = circuit.cost AndOr.andCost :=
      by exact_mod_cast
        pairCoverOfCircuit_cost problem admissible circuit constructs

end Fusion
end Algebraic
