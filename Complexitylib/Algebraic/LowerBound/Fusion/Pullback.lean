/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Fusion.Semifilter

/-!
# Pulling fusion covers back along a counterexample section

A semi-filter argument often studies a circuit over one ambient space while
the combinatorial cover lives over the complement of a different target.  A
`SemifilterPullback` records the bridge:

* a section from source counterexamples into the circuit's ambient space;
* a reference point in the circuit space for each source witness;
* soundness of every circuit generator under pullback; and
* separation of the target from the image of the section.

Every target circuit then gives a pair cover of the source problem.  The pair
associated with an AND gate is obtained by pulling its two argument sets back
along the section, and the cover cost is exactly the circuit's AND cost.
-/

@[expose] public section

namespace Algebraic
namespace Fusion

variable {Γ Δ : Type*}

/-- Data transporting semi-filter witnesses from `source` to a set
construction problem `target`. -/
structure SemifilterPullback
    (source : SetProblem Γ)
    (target : SetProblem Δ)
    (admissible : SemifilterClass source) where
  /-- Embed each source counterexample into the target ambient space. -/
  counterexampleMap : Problem.Outside source → Δ
  /-- Reference point used for a particular source witness. -/
  referencePoint : SemifilterWitness source admissible → Δ
  /-- Reference-true target generators pull back to accepted source sets. -/
  input_sound : ∀ witness input,
    referencePoint witness ∈ target.inputs input →
      counterexampleMap ⁻¹' target.inputs input ∈ witness.filter
  /-- Every reference point belongs to the target. -/
  target_reference : ∀ witness,
    referencePoint witness ∈ target.target
  /-- The counterexample section avoids the target. -/
  section_avoids_target : ∀ counterexample,
    counterexampleMap counterexample ∉ target.target

variable {source : SetProblem Γ}
variable {target : SetProblem Δ}
variable {admissible : SemifilterClass source}

/-- Observation model induced by a semi-filter pullback. -/
def SemifilterPullback.model
    (pullback : SemifilterPullback source target admissible) :
    Model AndOr.andCost (AndOr.setInterpretation Δ) target where
  Witness := SemifilterWitness source admissible
  reference witness set := pullback.referencePoint witness ∈ set
  observed witness set := pullback.counterexampleMap ⁻¹' set ∈ witness.filter
  input_sound := pullback.input_sound
  target_reference := pullback.target_reference
  target_not_observed := by
    intro witness
    have preimageEmpty : pullback.counterexampleMap ⁻¹' target.target = ∅ := by
      ext counterexample
      simp [pullback.section_avoids_target counterexample]
    rw [preimageEmpty]
    exact witness.filter.empty_not_mem

/-- The pulled-back pair contributed by an AND atom. -/
def Atom.pullbackPair?
    (pullback : SemifilterPullback source target admissible)
    (atom : Atom AndOr.signature (Set Δ)) : Option (Pair source) :=
  match atom with
  | ⟨.and, arguments⟩ => some
      (pullback.counterexampleMap ⁻¹' arguments ⟨0, by decide⟩,
        pullback.counterexampleMap ⁻¹' arguments ⟨1, by decide⟩)
  | ⟨.or, _⟩ => none

@[simp] theorem Atom.pullbackPair?_and
    (pullback : SemifilterPullback source target admissible)
    (arguments : Fin (AndOr.signature.Arity .and) → Set Δ) :
    Atom.pullbackPair? pullback (⟨.and, arguments⟩ :
      Atom AndOr.signature (Set Δ)) =
      some (pullback.counterexampleMap ⁻¹' arguments ⟨0, by decide⟩,
        pullback.counterexampleMap ⁻¹' arguments ⟨1, by decide⟩) := rfl

@[simp] theorem Atom.pullbackPair?_or
    (pullback : SemifilterPullback source target admissible)
    (arguments : Fin (AndOr.signature.Arity .or) → Set Δ) :
    Atom.pullbackPair? pullback (⟨.or, arguments⟩ :
      Atom AndOr.signature (Set Δ)) = none := rfl

/-- Pull back all intersection pairs from a list of target atoms. -/
def SemifilterPullback.pairs
    (pullback : SemifilterPullback source target admissible)
    (atoms : List (Atom AndOr.signature (Set Δ))) : List (Pair source) :=
  atoms.filterMap (Atom.pullbackPair? pullback)

@[simp] theorem SemifilterPullback.pairs_cons_and
    (pullback : SemifilterPullback source target admissible)
    (arguments : Fin (AndOr.signature.Arity .and) → Set Δ)
    (atoms : List (Atom AndOr.signature (Set Δ))) :
    pullback.pairs (⟨.and, arguments⟩ :: atoms) =
      (pullback.counterexampleMap ⁻¹' arguments ⟨0, by decide⟩,
        pullback.counterexampleMap ⁻¹' arguments ⟨1, by decide⟩) ::
          pullback.pairs atoms := by
  unfold SemifilterPullback.pairs
  rw [List.filterMap_cons_some
    (Atom.pullbackPair?_and pullback arguments)]

@[simp] theorem SemifilterPullback.pairs_cons_or
    (pullback : SemifilterPullback source target admissible)
    (arguments : Fin (AndOr.signature.Arity .or) → Set Δ)
    (atoms : List (Atom AndOr.signature (Set Δ))) :
    pullback.pairs (⟨.or, arguments⟩ :: atoms) =
      pullback.pairs atoms := by
  unfold SemifilterPullback.pairs
  rw [List.filterMap_cons_none
    (Atom.pullbackPair?_or pullback arguments)]

/-- Pulled-back pair count is the AND weight of the atoms. -/
theorem SemifilterPullback.pairs_length
    (pullback : SemifilterPullback source target admissible)
    (atoms : List (Atom AndOr.signature (Set Δ))) :
    (pullback.pairs atoms).length =
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

/-- Preserving an atom's pulled-back pair is enough to preserve the atom in
the pullback observation model. -/
theorem Atom.preservedBy_pullbackModel
    (pullback : SemifilterPullback source target admissible)
    (atom : Atom AndOr.signature (Set Δ))
    (witness : SemifilterWitness source admissible)
    (pairPreserved : ∀ pair,
      atom.pullbackPair? pullback = some pair →
        witness.filter.PreservesPair pair) :
    atom.PreservedBy pullback.model witness := by
  cases atom with
  | mk op arguments =>
      cases op with
      | and =>
          simp only [Atom.PreservedBy, Model.Sound, Atom.result,
            SemifilterPullback.model, AndOr.setInterpretation,
            Set.preimage_inter, Set.mem_inter_iff] at *
          intro argumentsSound referenceResult
          have leftObserved := argumentsSound ⟨0, by decide⟩ referenceResult.1
          have rightObserved := argumentsSound ⟨1, by decide⟩ referenceResult.2
          exact pairPreserved _ rfl leftObserved rightObserved
      | or =>
          simp only [Atom.PreservedBy, Model.Sound, Atom.result,
            SemifilterPullback.model, AndOr.setInterpretation,
            Set.preimage_union, Set.mem_union] at *
          intro argumentsSound referenceResult
          rcases referenceResult with leftReference | rightReference
          · exact witness.filter.union_right _
              (argumentsSound ⟨0, by decide⟩ leftReference)
          · exact witness.filter.union_left _
              (argumentsSound ⟨1, by decide⟩ rightReference)

/-- A constructing target circuit yields a pair cover of the source problem. -/
def SemifilterPullback.pairCoverOfCircuit
    (pullback : SemifilterPullback source target admissible)
    (circuit : Circuit AndOr.signature target.inputCount g 1)
    (constructs : target.Constructs circuit (AndOr.setInterpretation Δ)) :
    PairCover source admissible where
  pairs := pullback.pairs
    (circuitAtoms circuit (AndOr.setInterpretation Δ) target.inputs)
  isCover := by
    intro point pointMem filter filterAdmissible above preservesPairs
    let witness : SemifilterWitness source admissible :=
      { point := point
        point_mem := pointMem
        filter := filter
        admissible_filter := filterAdmissible
        above := above }
    let genericCover := coverOfCircuit pullback.model circuit constructs
    apply genericCover.isCover witness
    intro atom atomMem
    apply atom.preservedBy_pullbackModel pullback witness
    intro pair equal
    apply preservesPairs pair
    change atom ∈ circuitAtoms circuit (AndOr.setInterpretation Δ)
      target.inputs at atomMem
    simp only [SemifilterPullback.pairs, List.mem_filterMap]
    exact ⟨atom, atomMem, equal⟩

/-- Pullback preserves the exact AND cost of a constructing circuit. -/
theorem SemifilterPullback.pairCoverOfCircuit_cost
    (pullback : SemifilterPullback source target admissible)
    (circuit : Circuit AndOr.signature target.inputCount g 1)
    (constructs : target.Constructs circuit (AndOr.setInterpretation Δ)) :
    (pullback.pairCoverOfCircuit circuit constructs).cost =
      circuit.cost AndOr.andCost := by
  rw [PairCover.cost, SemifilterPullback.pairCoverOfCircuit,
    SemifilterPullback.pairs_length]
  exact circuitAtoms_cost circuit (AndOr.setInterpretation Δ)
    target.inputs AndOr.andCost

/-- A lower bound for source pair covers transfers across a pullback to every
constructing target circuit. -/
theorem SemifilterPullback.lowerBound
    (pullback : SemifilterPullback source target admissible)
    (coverLowerBound : ∀ cover : PairCover source admissible,
      L ≤ cover.cost)
    (circuit : Circuit AndOr.signature target.inputCount g 1)
    (constructs : target.Constructs circuit (AndOr.setInterpretation Δ)) :
    L ≤ circuit.cost AndOr.andCost := by
  rw [← pullback.pairCoverOfCircuit_cost circuit constructs]
  exact coverLowerBound (pullback.pairCoverOfCircuit circuit constructs)

end Fusion
end Algebraic
