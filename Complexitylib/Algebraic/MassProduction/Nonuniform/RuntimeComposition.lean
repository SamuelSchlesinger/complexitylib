/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.MassProduction.Nonuniform.ScheduledRecovery
public import Complexitylib.Algebraic.MassProduction.HighRate.PrefixMetadata
public import Complexitylib.Algebraic.MassProduction.RuntimePipeline

/-!
# Complete nonuniform mass-production circuit on raw request inputs

The shared prefix table supplies the code placement metadata, while fixed
wiring retains each suffix. The scheduler and resource pipeline then compute
the direct product of the requested Boolean function. The finite bound
includes every runtime stage and the exact sum of resource-circuit costs.
-/

@[expose] public section

namespace Algebraic.MassProduction.Nonuniform.RuntimeComposition

open Sorting HighRate RuntimePipeline
open scoped LinearAlgebra.Projectivization

variable {memberGates : Fin (ResourceLayout.count copies dimension width) → Nat}

set_option backward.isDefEq.respectTransparency false

/-- Complete runtime overhead apart from the actual resource evaluations. -/
def overhead (depth copies prefixWidth dimension width suffixWidth copyBits selectorBits : Nat) : Nat :=
  PrefixMetadata.costBound (networkRecords depth) prefixWidth dimension width copyBits selectorBits +
    ScheduledRecovery.overhead depth copies dimension width
      (PrefixMetadata.payloadWidth dimension width copyBits selectorBits suffixWidth) copyBits selectorBits suffixWidth

/-- One circuit computes all raw prefix/suffix requests, including repeated
requests, with no unproved scheduler, encoding, or routing premise. -/
theorem existsCircuit
    (positive : 0 < width) (dimensionPositive : 0 < dimension)
    (budget : 512 * networkRecords depth * Nat.card (BinaryExtension width) ≤
      Nat.card (ℙ (BinaryExtension width) (Fin dimension → BinaryExtension width)))
    (code : LineCode (BinaryExtension width) (Fin dimension))
    (placement : Fin (2 ^ prefixWidth) ↪ InformationBit code copies)
    (function : Fin (2 ^ prefixWidth) → (Fin suffixWidth → Bool) → Bool)
    (copyFits : copies ≤ 2 ^ copyBits) (selectorFits : width ≤ 2 ^ selectorBits)
    (members : (resource : Fin (ResourceLayout.count copies dimension width)) →
      Circuit DeMorgan.signature suffixWidth (memberGates resource) 1)
    (membersCorrect : ∀ resource suffix,
      (members resource).eval DeMorgan.interpretation suffix 0 =
        ResourceLayout.function positive code placement function resource suffix) :
    ∃ gates, ∃ result : Circuit DeMorgan.signature (networkRecords depth * (prefixWidth + suffixWidth)) gates
      (networkRecords depth),
      result.cost DeMorgan.standardCost ≤ overhead depth copies prefixWidth dimension width suffixWidth copyBits selectorBits +
        ∑ resource, (members resource).cost DeMorgan.standardCost ∧
      result.ComputesWith DeMorgan.interpretation (directProduct (requestFunction function) (networkRecords depth)) := by
  obtain ⟨preparationGates, preparation, preparationBound, preparationCorrect⟩ := PrefixMetadata.existsCircuit
    positive code placement (networkRecords depth) suffixWidth copyBits selectorBits
  let original := fun (request : Fin (networkRecords depth))
      (bit : Fin (PrefixMetadata.payloadWidth dimension width copyBits selectorBits suffixWidth)) =>
    (DeMorgan.Wiring.input (finProdFinEquiv (request, bit)) :
      DeMorgan.Wiring (networkRecords depth * PrefixMetadata.payloadWidth dimension width copyBits selectorBits suffixWidth))
  obtain ⟨recoveryGates, recovery, recoveryBound, recoveryCorrect⟩ := ScheduledRecovery.existsCircuit
    positive dimensionPositive budget code placement function copyFits selectorFits original
    (PrefixMetadata.targetProjection dimension width copyBits selectorBits suffixWidth)
    (PrefixMetadata.copyProjection dimension width copyBits selectorBits suffixWidth)
    (PrefixMetadata.selectorProjection dimension width copyBits selectorBits suffixWidth)
    (PrefixMetadata.suffixProjection dimension width copyBits selectorBits suffixWidth) members membersCorrect
  refine ⟨_, recovery.comp preparation, ?_, ?_⟩
  · rw [Circuit.cost_comp]
    exact (Nat.add_le_add preparationBound recoveryBound).trans_eq (by unfold overhead; omega)
  · intro input
    funext request
    rw [Circuit.eval_comp, directProduct_requestFunction_apply]
    apply recoveryCorrect (preparation.eval DeMorgan.interpretation input) (requestSource input) (requestSuffix input)
    · intro position bit
      simp only [original, DeMorgan.Wiring.eval_input, preparationCorrect,
        PrefixMetadata.targetProjection, PrefixMetadata.metadata, Fin.append_left]
    · intro position bit
      simp only [original, DeMorgan.Wiring.eval_input, preparationCorrect,
        PrefixMetadata.copyProjection, PrefixMetadata.metadata, Fin.append_left, Fin.append_right]
    · intro position bit
      simp only [original, DeMorgan.Wiring.eval_input, preparationCorrect,
        PrefixMetadata.selectorProjection, PrefixMetadata.metadata, Fin.append_left, Fin.append_right]
    · intro position bit
      simp only [original, DeMorgan.Wiring.eval_input, preparationCorrect,
        PrefixMetadata.suffixProjection, Fin.append_right]

/-- The concrete runtime construction bounds Boolean mass complexity by
its full overhead plus one evaluation of every actual resource function. -/
theorem booleanMassComplexity_le
    (positive : 0 < width) (dimensionPositive : 0 < dimension)
    (budget : 512 * networkRecords depth * Nat.card (BinaryExtension width) ≤
      Nat.card (ℙ (BinaryExtension width) (Fin dimension → BinaryExtension width)))
    (code : LineCode (BinaryExtension width) (Fin dimension))
    (placement : Fin (2 ^ prefixWidth) ↪ InformationBit code copies)
    (function : Fin (2 ^ prefixWidth) → (Fin suffixWidth → Bool) → Bool)
    (copyFits : copies ≤ 2 ^ copyBits) (selectorFits : width ≤ 2 ^ selectorBits)
    (members : (resource : Fin (ResourceLayout.count copies dimension width)) →
      Circuit DeMorgan.signature suffixWidth (memberGates resource) 1)
    (membersCorrect : ∀ resource suffix,
      (members resource).eval DeMorgan.interpretation suffix 0 =
        ResourceLayout.function positive code placement function resource suffix)
    (memberBound : ∀ resource, (members resource).cost DeMorgan.standardCost ≤ resourceBound) :
    booleanMassComplexity (requestFunction function) (networkRecords depth) ≤
      (overhead depth copies prefixWidth dimension width suffixWidth copyBits selectorBits +
        ResourceLayout.count copies dimension width * resourceBound : Nat) := by
  obtain ⟨gates, result, bound, computes⟩ := existsCircuit positive dimensionPositive budget code placement
    function copyFits selectorFits members membersCorrect
  have sumBound : (∑ resource, (members resource).cost DeMorgan.standardCost) ≤
      ResourceLayout.count copies dimension width * resourceBound := by
    calc
      _ ≤ ∑ _resource : Fin (ResourceLayout.count copies dimension width), resourceBound :=
        Finset.sum_le_sum (fun resource _ => memberBound resource)
      _ = _ := by simp
  have totalBound := bound.trans (Nat.add_le_add_left sumBound _)
  exact (result.costComplexity_le DeMorgan.standardCost computes).trans (by exact_mod_cast totalBound)

end Algebraic.MassProduction.Nonuniform.RuntimeComposition
