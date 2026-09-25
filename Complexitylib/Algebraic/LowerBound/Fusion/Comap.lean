/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Fusion.Framework

/-!
# Transporting fusion models along homomorphisms

A homomorphism of interpretations sends every circuit constructing a problem
to a circuit constructing the homomorphic image of that problem, with the same
gates.  Consequently a fusion model for the image problem yields a fusion model
for the source problem: witnesses are unchanged and both predicates are read
through the homomorphism.  Atoms of the source circuit map to atoms of the
image circuit, so covers transport with exactly the same operation cost.

This is the basic bridge for lower bounds that observe a circuit only after a
restriction, a quotient, or another structure-preserving projection of its
semantic values.  Each homomorphism yields one transported lower bound;
combining several images requires additional accounting.
-/

@[expose] public section

namespace Algebraic
namespace Fusion

/-- Push a construction problem forward along a map of carriers. -/
def Problem.map (problem : Problem U₁) (f : U₁ → U₂) : Problem U₂ where
  inputCount := problem.inputCount
  inputs := f ∘ problem.inputs
  target := f problem.target

@[simp] theorem Problem.map_inputCount
    (problem : Problem U₁) (f : U₁ → U₂) :
    (problem.map f).inputCount = problem.inputCount := rfl

@[simp] theorem Problem.map_inputs
    (problem : Problem U₁) (f : U₁ → U₂) (input : Fin problem.inputCount) :
    (problem.map f).inputs input = f (problem.inputs input) := rfl

@[simp] theorem Problem.map_target
    (problem : Problem U₁) (f : U₁ → U₂) :
    (problem.map f).target = f problem.target := rfl

/-- A circuit constructing a problem constructs its homomorphic image. -/
theorem Problem.Constructs.map
    {i₁ : Interpretation σ U₁}
    {i₂ : Interpretation σ U₂}
    (h : Homomorphism i₁ i₂)
    {problem : Problem U₁}
    {circuit : Circuit σ problem.inputCount 1}
    (constructs : problem.Constructs circuit i₁) :
    (problem.map h.map).Constructs circuit i₂ := by
  unfold Problem.Constructs at constructs ⊢
  have commutes := congrFun (circuit.map_eval h problem.inputs) 0
  change circuit.eval i₂ (h.map ∘ problem.inputs) 0 = h.map problem.target
  rw [← commutes, Function.comp_apply, constructs]

/-- Apply a carrier map to every argument of an atom. -/
def Atom.map (atom : Atom σ U₁) (f : U₁ → U₂) : Atom σ U₂ where
  op := atom.op
  arguments := f ∘ atom.arguments

@[simp] theorem Atom.map_op
    (atom : Atom σ U₁) (f : U₁ → U₂) :
    (atom.map f).op = atom.op := rfl

@[simp] theorem Atom.map_arguments
    (atom : Atom σ U₁) (f : U₁ → U₂) :
    (atom.map f).arguments = f ∘ atom.arguments := rfl

@[simp] theorem Atom.map_cost
    (atom : Atom σ U₁) (f : U₁ → U₂) (operationCost : OperationCost σ) :
    (atom.map f).cost operationCost = atom.cost operationCost := rfl

/-- Mapping atoms preserves the total weight of a list. -/
theorem Atom.listCost_map
    (atoms : List (Atom σ U₁)) (f : U₁ → U₂) (operationCost : OperationCost σ) :
    Atom.listCost (atoms.map fun atom => atom.map f) operationCost =
      Atom.listCost atoms operationCost := by
  simp [Atom.listCost, List.map_map, Function.comp_def]

/-- The result of a mapped atom is the image of the original result. -/
theorem Atom.map_result
    {i₁ : Interpretation σ U₁}
    {i₂ : Interpretation σ U₂}
    (h : Homomorphism i₁ i₂)
    (atom : Atom σ U₁) :
    (atom.map h.map).result i₂ = h.map (atom.result i₁) := by
  unfold Atom.result Atom.map
  exact (h.homomorphic atom.op atom.arguments).symm

/-- Pull a fusion model for the homomorphic image of a problem back to the
source problem.  Witnesses are unchanged; both predicates are evaluated on the
image of a semantic value.  The view is reducible so that the witness type of
the pulled-back model is recognized as the witness type of the image model. -/
abbrev Model.comap
    {i₁ : Interpretation σ U₁}
    {i₂ : Interpretation σ U₂}
    (h : Homomorphism i₁ i₂)
    {operationCost : OperationCost σ}
    {problem : Problem U₁}
    (model : Model operationCost i₂ (problem.map h.map)) :
    Model operationCost i₁ problem where
  Witness := model.Witness
  reference witness value := model.reference witness (h.map value)
  observed witness value := model.observed witness (h.map value)
  input_sound witness input := model.input_sound witness input
  target_reference := model.target_reference
  target_not_observed := model.target_not_observed

section Comap

variable {i₁ : Interpretation σ U₁}
variable {i₂ : Interpretation σ U₂}
variable {operationCost : OperationCost σ}
variable {problem : Problem U₁}

/-- A witness preserves an atom in the pulled-back model exactly when it
preserves the mapped atom in the image model. -/
theorem Atom.preservedBy_comap_iff
    (h : Homomorphism i₁ i₂)
    (model : Model operationCost i₂ (problem.map h.map))
    (atom : Atom σ U₁)
    (witness : model.Witness) :
    atom.PreservedBy (model.comap h) witness ↔
      (atom.map h.map).PreservedBy model witness := by
  unfold Atom.PreservedBy
  rw [Atom.map_result]
  exact Iff.rfl

/-- Push a cover of the pulled-back model forward to the image model. -/
def Cover.map
    (h : Homomorphism i₁ i₂)
    {model : Model operationCost i₂ (problem.map h.map)}
    (cover : Cover (model.comap h)) : Cover model where
  atoms := cover.atoms.map fun atom => atom.map h.map
  isCover := by
    intro witness preserves
    apply cover.isCover witness
    intro atom present
    rw [Atom.preservedBy_comap_iff]
    exact preserves (atom.map h.map) (List.mem_map.mpr ⟨atom, present, rfl⟩)

/-- Pushing a cover forward preserves its cost. -/
@[simp] theorem Cover.map_cost
    (h : Homomorphism i₁ i₂)
    {model : Model operationCost i₂ (problem.map h.map)}
    (cover : Cover (model.comap h)) :
    (cover.map h).cost = cover.cost :=
  Atom.listCost_map cover.atoms h.map operationCost

/-- Cover complexity can only grow when a model is pulled back. -/
theorem Model.coverComplexity_le_comap
    (h : Homomorphism i₁ i₂)
    (model : Model operationCost i₂ (problem.map h.map)) :
    model.coverComplexity ≤ (model.comap h).coverComplexity := by
  unfold Model.coverComplexity
  refine le_iInf fun cover => ?_
  calc
    (⨅ imageCover : Cover model, (imageCover.cost : ℕ∞)) ≤
        ((cover.map h).cost : ℕ∞) := iInf_le _ _
    _ = cover.cost := by rw [Cover.map_cost]

/-- A framework for the image model is a framework for the pulled-back model. -/
def Framework.comap
    (h : Homomorphism i₁ i₂)
    {model : Model operationCost i₂ (problem.map h.map)}
    (framework : Framework model) : Framework (model.comap h) where
  bound := framework.bound
  coverLowerBound cover := by
    rw [← Cover.map_cost h cover]
    exact framework.coverLowerBound (cover.map h)

@[simp] theorem Framework.comap_bound
    (h : Homomorphism i₁ i₂)
    {model : Model operationCost i₂ (problem.map h.map)}
    (framework : Framework model) :
    (framework.comap h).bound = framework.bound := rfl

/-- A fusion lower bound for the homomorphic image of a problem is a lower
bound for every circuit constructing the source problem. -/
theorem Framework.lowerBound_of_map
    (h : Homomorphism i₁ i₂)
    {model : Model operationCost i₂ (problem.map h.map)}
    (framework : Framework model)
    (circuit : Circuit σ problem.inputCount 1)
    (constructs : problem.Constructs circuit i₁) :
    framework.bound ≤ circuit.cost operationCost :=
  framework.lowerBound circuit (constructs.map h)

/-- Cover complexity of an image model lower-bounds every source circuit. -/
theorem Model.coverComplexity_le_cost_of_map
    (h : Homomorphism i₁ i₂)
    (model : Model operationCost i₂ (problem.map h.map))
    (circuit : Circuit σ problem.inputCount 1)
    (constructs : problem.Constructs circuit i₁) :
    model.coverComplexity ≤ circuit.cost operationCost :=
  model.coverComplexity_le_cost circuit (constructs.map h)

end Comap

end Fusion
end Algebraic
