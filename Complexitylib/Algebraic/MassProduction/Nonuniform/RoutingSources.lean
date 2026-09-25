/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.MassProduction.RoutingRecords

/-!
# Identifying source records without key uniqueness

In the packed routing layout, the false tag identifies exactly the source
prefix. Source keys and payloads may repeat arbitrarily.
-/

@[expose] public section

namespace Algebraic.MassProduction.Nonuniform.Broadcast

open Sorting

/-- Every false-tagged raw routing record is one of the declared sources. -/
theorem routingRecordSequence_sourceOfTag
    (sourceKeys : Fin sourceCount → Fin keyWidth → Bool)
    (sourcePayloads : Fin sourceCount → Fin payloadWidth → Bool)
    (destinationKeys : Fin destinationCount → Fin keyWidth → Bool)
    (destinationPayloads : Fin destinationCount → Fin payloadWidth → Bool)
    (paddingKeys : Fin paddingCount → Fin keyWidth → Bool)
    (paddingPayloads : Fin paddingCount → Fin payloadWidth → Bool)
    (index : Fin (sourceCount + destinationCount + paddingCount))
    (sourceTag : Routing.packedRecordTag
      (Routing.routingRecordSequence sourceKeys sourcePayloads destinationKeys
        destinationPayloads paddingKeys paddingPayloads index) = false) :
    ∃ source, Routing.routingRecordSequence sourceKeys sourcePayloads destinationKeys
      destinationPayloads paddingKeys paddingPayloads index =
        Routing.packRecord (sourceKeys source) false (sourcePayloads source) := by
  revert sourceTag
  unfold Routing.routingRecordSequence
  refine Fin.addCases (fun active => ?_) (fun padding => ?_) index
  · simp only [Fin.append_left]
    refine Fin.addCases (fun source => ?_) (fun destination => ?_) active
    · simp only [Fin.append_left, Routing.packedRecordTag_packRecord]
      intro _
      exact ⟨source, rfl⟩
    · simp only [Fin.append_right, Routing.packedRecordTag_packRecord, Bool.true_eq_false,
        false_implies]
  · simp only [Fin.append_right, Routing.packedRecordTag_packRecord, Bool.true_eq_false,
      false_implies]

/-- The same source classification holds after casting and flattening to
the exact power-of-two routing capacity. -/
theorem routingInputBits_sourceOfTag
    (sourceKeys : Fin sourceCount → Fin keyWidth → Bool)
    (sourcePayloads : Fin sourceCount → Fin payloadWidth → Bool)
    (destinationKeys : Fin destinationCount → Fin keyWidth → Bool)
    (destinationPayloads : Fin destinationCount → Fin payloadWidth → Bool)
    (paddingKeys : Fin paddingCount → Fin keyWidth → Bool)
    (paddingPayloads : Fin paddingCount → Fin payloadWidth → Bool)
    (recordCount : sourceCount + destinationCount + paddingCount = networkRecords depth)
    (index : Fin (networkRecords depth))
    (sourceTag : Routing.recordTag
      (Routing.routingInputBits sourceKeys sourcePayloads destinationKeys
        destinationPayloads paddingKeys paddingPayloads recordCount) index = false) :
    ∃ source, flatRecords
      (Routing.routingInputBits sourceKeys sourcePayloads destinationKeys
        destinationPayloads paddingKeys paddingPayloads recordCount) index =
        Routing.packRecord (sourceKeys source) false (sourcePayloads source) := by
  have tag : Routing.packedRecordTag (flatRecords
      (Routing.routingInputBits sourceKeys sourcePayloads destinationKeys
        destinationPayloads paddingKeys paddingPayloads recordCount) index) = false := sourceTag
  rw [Routing.flatRecords_routingInputBits] at tag ⊢
  exact routingRecordSequence_sourceOfTag sourceKeys sourcePayloads destinationKeys
    destinationPayloads paddingKeys paddingPayloads (Fin.cast recordCount.symm index) tag

end Algebraic.MassProduction.Nonuniform.Broadcast
