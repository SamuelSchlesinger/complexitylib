/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.MassProduction.IncidenceRouting
public import Complexitylib.Algebraic.MassProduction.RoutingWiring

/-!
# Scheduled-incidence routing wiring

This module identifies each affine-point bit in the grouped scheduler output
with the corresponding incidence-key wire.  It is the narrow bridge from the
semantic schedule to the zero-cost routing-record wiring layer; assembly of
the scatter and gather records is kept in the focused `ScatterAssembly` and
`GatherAssembly` modules.
-/

@[expose] public section

namespace Algebraic
namespace MassProduction
namespace RoutingAssembly

open GroupedScheduler
open IncidenceRouting
open LineEnumeration
open SchedulerIteration

/-- Number of Boolean wires in one grouped scheduler output. -/
@[reducible] noncomputable def scheduleBitCount
    (groups requestsPerGroup dimension width : Nat) : Nat :=
  groups * (requestsPerGroup * lineBitWidth dimension width)

/-- Scheduler-output wire containing one affine-point bit of a flattened
scheduled incidence. -/
noncomputable def scheduledIncidencePointBitIndex
    (capacity : totalRequests <= groups * requestsPerGroup)
    (incidence : Fin (totalRequests * nonzeroScalarCount width))
    (pointBit : Fin (dimension * width)) :
    Fin (scheduleBitCount groups requestsPerGroup dimension width) :=
  let requestAndScalar := incidenceAt incidence
  let groupAndRequest := requestGroupSlot capacity requestAndScalar.1
  finProdFinEquiv
    (groupAndRequest.1,
      finProdFinEquiv
        (groupAndRequest.2,
          finProdFinEquiv (requestAndScalar.2, pointBit)))

/-- Decoding and re-encoding a scheduled point is exactly the corresponding
scheduler-output block. -/
theorem scheduledIncidencePointBit
    (widthPositive : 0 < width)
    (capacity : totalRequests <= groups * requestsPerGroup)
    (scheduleOutput :
      Fin (scheduleBitCount groups requestsPerGroup dimension width) -> Bool)
    (incidence : Fin (totalRequests * nonzeroScalarCount width))
    (pointBit : Fin (dimension * width)) :
    binaryExtensionVectorBits widthPositive
        (scheduledIncidenceSlotAt widthPositive capacity scheduleOutput
          incidence).2 pointBit =
      scheduleOutput
        (scheduledIncidencePointBitIndex capacity incidence pointBit) := by
  unfold scheduledIncidenceSlotAt scheduledIncidenceSlot
  unfold requestScheduledLinePoint scheduledLinePoint
  rw [binaryExtensionVectorBits_vectorCoordinate]
  rfl

/-- Scheduled matching keys are a constant active marker and group prefix
followed by scheduler-output point wires. -/
theorem scheduledIncidenceKeyBits_eq_wiring
    (widthPositive : 0 < width)
    (groupBitWidth : Nat)
    (capacity : totalRequests <= groups * requestsPerGroup)
    (scheduleOutput :
      Fin (scheduleBitCount groups requestsPerGroup dimension width) -> Bool)
    (incidence : Fin (totalRequests * nonzeroScalarCount width)) :
    scheduledIncidenceKeyBits widthPositive groupBitWidth capacity
        scheduleOutput incidence =
      activeRoutingKey (Fin.append
        (finiteIndexBits groupBitWidth
          (scheduledIncidenceSlotAt widthPositive capacity scheduleOutput
            incidence).1)
        (fun pointBit => scheduleOutput
          (scheduledIncidencePointBitIndex capacity incidence pointBit))) := by
  unfold scheduledIncidenceKeyBits
  apply congrArg activeRoutingKey
  unfold resourceSlotKeyBits
  funext baseBit
  refine Fin.addCases (fun groupBit => ?_) (fun pointBit => ?_) baseBit
  · rw [Fin.append_left, Fin.append_left]
  · rw [Fin.append_right, Fin.append_right]
    exact scheduledIncidencePointBit widthPositive capacity scheduleOutput
      incidence pointBit

end RoutingAssembly
end MassProduction
end Algebraic
