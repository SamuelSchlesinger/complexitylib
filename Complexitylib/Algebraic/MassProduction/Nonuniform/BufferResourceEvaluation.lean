/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.MassProduction.Nonuniform.BufferResourceWires
public import Complexitylib.Algebraic.MassProduction.Nonuniform.IncidenceEvaluation
public import Complexitylib.Algebraic.MassProduction.Nonuniform.MaskedXor

/-!
# High-rate resource recovery from a completed scheduler buffer

This circuit reads preserved copy, basis-bit, and suffix metadata, scatters
the suffixes to the exact resource bank, evaluates each resource once,
gathers its point values, and XORs each recovery line. It computes the
requested source function in completed-buffer order, with the original
request permutation still available in the buffer.
-/

@[expose] public section

namespace Algebraic.MassProduction.Nonuniform.BufferResourceEvaluation

open BufferInput BufferModel HighRate
open scoped LinearAlgebra.Projectivization

variable {Source : Type*}

set_option backward.isDefEq.respectTransparency false

/-- Information-point targets determined by each original source request. -/
def targets (code : LineCode (BinaryExtension width) (Fin dimension))
    (placement : Source ↪ InformationBit code copies) (sources : Fin total → Source) :
    Fin total → Fin dimension → BinaryExtension width :=
  fun request => (placement (sources request)).2.1.val

/-- Evaluate and recover every completed request using one exact bank.
The only input-dependent premise is that the buffer correctly represents a
disjoint schedule and the source/copy/selector/suffix metadata. -/
theorem existsCircuit
    (positive : 0 < width)
    (code : LineCode (BinaryExtension width) (Fin dimension))
    (placement : Source ↪ InformationBit code copies)
    (function : Source → (Fin suffixWidth → Bool) → Bool)
    (copyFits : copies ≤ 2 ^ copyBits) (selectorFits : width ≤ 2 ^ selectorBits)
    (copyProjection : Fin copyBits → Fin requestWidth)
    (selectorProjection : Fin selectorBits → Fin requestWidth)
    (suffixProjection : Fin suffixWidth → Fin requestWidth)
    (members : (resource : Fin (ResourceLayout.count copies dimension width)) →
      Circuit DeMorgan.signature suffixWidth 1)
    (membersCorrect : ∀ resource suffix,
      (members resource).eval DeMorgan.interpretation suffix 0 =
        ResourceLayout.function positive code placement function resource suffix) :
    ∃ recovered : Circuit DeMorgan.signature
      (inputWidth total 0 requestWidth (2 ^ width) (dimension * width)) total,
      recovered.cost DeMorgan.standardCost ≤
        IncidenceEvaluation.routingCost (total * 2 ^ width) (ResourceLayout.count copies dimension width)
          (ResourceLayout.keyWidth copyBits dimension width selectorBits) suffixWidth +
        (∑ resource, (members resource).cost DeMorgan.standardCost) + total * 2 ^ width * 4 ∧
      ∀ (data : Fin total → Fin requestWidth → Bool) (sources : Fin total → Source)
        (suffixes : Fin total → Fin suffixWidth → Bool)
        (state : State total total 0 dimension width),
        WellScheduled state (targets code placement sources) →
        (∀ request bit, data request (copyProjection bit) =
          finiteIndexBits copyBits (placement (sources request)).1 bit) →
        (∀ request bit, data request (selectorProjection bit) =
          finiteIndexBits selectorBits (placement (sources request)).2.2 bit) →
        (∀ request bit, data request (suffixProjection bit) = suffixes request bit) →
        ∀ request, recovered.eval DeMorgan.interpretation
          (input positive state data (targets code placement sources)) request =
            function (sources (state.order (.inl request))) (suffixes (state.order (.inl request))) := by
  obtain ⟨evaluated, bound, correct⟩ := IncidenceEvaluation.existsCircuit
    (incidenceValid (completed := total) positive)
    (BufferResourceWires.keys width dimension copyProjection selectorProjection)
    (BufferResourceWires.payload width dimension suffixProjection)
    (ResourceLayout.key copyBits selectorBits) (ResourceLayout.key_injective copyFits selectorFits) members
  refine ⟨(MaskedXor.circuit (PaddedLinePoints.valid positive) total).comp evaluated, ?_, ?_⟩
  · rw [Circuit.cost_comp, MaskedXor.circuit_cost]
    exact Nat.add_le_add_right bound _
  · intro data sources suffixes state scheduled copyCorrect selectorCorrect suffixCorrect request
    let input := BufferModel.input positive state data (targets code placement sources)
    rw [Circuit.eval_comp, MaskedXor.circuit_eval]
    have valuesCorrect :
        (∑ slot : Fin (2 ^ width), if PaddedLinePoints.valid positive slot then
          evaluated.eval DeMorgan.interpretation input (finProdFinEquiv (request, slot)) else false) =
        ∑ slot : Fin (2 ^ width), if PaddedLinePoints.valid positive slot then
          HighRate.booleanResource positive code placement function
            (placement (sources (state.order (.inl request)))).1
            (PaddedLinePoints.point positive
              (targets code placement sources (state.order (.inl request))) (state.directions request) slot)
            (placement (sources (state.order (.inl request)))).2.2 (suffixes (state.order (.inl request))) else false := by
      apply Finset.sum_congr rfl
      intro slot _
      split_ifs with active
      · let resource := ResourceLayout.position positive (placement (sources (state.order (.inl request)))).1
          (PaddedLinePoints.point positive
            (targets code placement sources (state.order (.inl request))) (state.directions request) slot)
          (placement (sources (state.order (.inl request)))).2.2
        have activeIncidence : incidenceValid positive (finProdFinEquiv (request, slot)) = true := by
          simpa only [incidenceValid, Equiv.symm_apply_apply] using active
        have keyCorrect := BufferResourceWires.keys_eval positive state data (targets code placement sources)
          copyProjection selectorProjection (fun request => (placement (sources request)).1)
          (fun request => (placement (sources request)).2.2) copyCorrect selectorCorrect request slot
        have unique : ∀ other, incidenceValid positive other = true →
            (fun bit => (BufferResourceWires.keys width dimension copyProjection selectorProjection other bit).eval input) =
              (fun bit => (BufferResourceWires.keys width dimension copyProjection selectorProjection
                (finProdFinEquiv (request, slot)) bit).eval input) → other = finProdFinEquiv (request, slot) := by
          intro other otherActive sameKey
          exact BufferResourceWires.activeKeys_injective positive state data (targets code placement sources)
            scheduled copyProjection selectorProjection other _ otherActive activeIncidence sameKey
        rw [correct input _ resource activeIncidence keyCorrect unique]
        have payloadCorrect :
            (fun bit => (BufferResourceWires.payload width dimension suffixProjection
              (finProdFinEquiv (request, slot)) bit).eval input) = suffixes (state.order (.inl request)) := by
          funext bit
          rw [BufferResourceWires.payload_eval, suffixCorrect]
        rw [payloadCorrect, membersCorrect]
        exact ResourceLayout.function_position positive code placement function _ _ _ _
      · rfl
    rw [valuesCorrect]
    exact PaddedLinePoints.booleanResourceRecovers positive code placement function
      (sources (state.order (.inl request))) (suffixes (state.order (.inl request))) (state.directions request)

end Algebraic.MassProduction.Nonuniform.BufferResourceEvaluation
