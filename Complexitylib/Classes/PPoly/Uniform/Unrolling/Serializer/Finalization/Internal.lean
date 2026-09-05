/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Classes.PPoly.Uniform.Unrolling.Serializer.Finalization.Defs
public import Complexitylib.Classes.PPoly.Uniform.Unrolling.Serializer.Initialization
public import Complexitylib.Classes.PPoly.Uniform.Unrolling.Stream
public import Complexitylib.Classes.PPoly.Uniform.Unrolling.Padded.Defs

/-!
# Numeric direct-tableau finalization -- proof internals
-/


public section

namespace Complexity

namespace CircuitUnrolling

namespace Serializer

theorem numericAcceptanceGate_eq_acceptanceGate_internal (tm : TM k)
    (T finalConfigBase : ℕ) :
    numericAcceptanceGate (Fintype.card tm.Q)
        (stateIndex tm.toNTM tm.qhalt) (k + 2) T finalConfigBase =
      acceptanceGate tm.toNTM T finalConfigBase := by
  simp [numericAcceptanceGate, acceptanceGate, configWire, configIndex,
    TapeSlot.index, symbolIndex, TM.toNTM, Nat.add_assoc]
  rfl

theorem length_directPaddingSchedule_internal
    (originalRawGateCount closedBound : ℕ) :
    (directPaddingSchedule originalRawGateCount closedBound).length =
      closedBound - originalRawGateCount := by
  simp [directPaddingSchedule]

theorem getElem_directPaddingSchedule_internal
    (originalRawGateCount closedBound : ℕ)
    (index : Fin (closedBound - originalRawGateCount)) :
    (directPaddingSchedule originalRawGateCount closedBound)[index.val]'(by
      rw [length_directPaddingSchedule_internal]
      exact index.isLt) = CircuitCode.RawGate.constant 0 false := by
  simp [directPaddingSchedule]

theorem length_directFinalizationSuffix_internal
    (n originalRawGateCount closedBound : ℕ) :
    (directFinalizationSuffix n originalRawGateCount closedBound).length =
      closedBound - originalRawGateCount + 1 := by
  simp [directFinalizationSuffix, length_directPaddingSchedule_internal]

theorem getElem_directFinalizationSuffix_padding_internal
    (n originalRawGateCount closedBound : ℕ)
    (index : Fin (closedBound - originalRawGateCount)) :
    (directFinalizationSuffix n originalRawGateCount closedBound)[index.val]'(by
      rw [length_directFinalizationSuffix_internal]
      omega) = CircuitCode.RawGate.constant 0 false := by
  unfold directFinalizationSuffix
  erw [List.getElem_append_left]
  exact getElem_directPaddingSchedule_internal originalRawGateCount closedBound index

theorem getElem_directFinalizationSuffix_terminal_internal
    (n originalRawGateCount closedBound : ℕ) :
    (directFinalizationSuffix n originalRawGateCount closedBound)[
        closedBound - originalRawGateCount]'(by
          rw [length_directFinalizationSuffix_internal]
          omega) = directTerminalCopyGate n originalRawGateCount := by
  unfold directFinalizationSuffix
  erw [List.getElem_append_right]
  · simp [length_directPaddingSchedule_internal]
  · rw [length_directPaddingSchedule_internal]

theorem directStepFragment_length_internal (tm : TM k) (T n : ℕ)
    (index : Fin T) :
    (tm.directStepFragment T n index).length = directStepSize tm.toNTM T := by
  simp [TM.directStepFragment]

theorem directUnrollingRawCircuit_length_eq_original_internal
    (tm : TM k) (f : ℕ → ℕ) (n : ℕ) [NeZero n] :
    (tm.directUnrollingRawCircuit f n).length =
      directOriginalRawGateCount tm (f n) := by
  rw [tm.directUnrollingRawCircuit_eq_init_append_steps]
  simp [directOriginalRawGateCount, directStepFragment_length_internal,
    Nat.add_assoc]

theorem paddedDirectUnrollingRawCircuit_eq_numericSchedule_internal
    (tm : TM k) (f : ℕ → ℕ) (n : ℕ) [NeZero n]
    (hn : n + 1 ≤ f n) :
    tm.paddedDirectUnrollingRawCircuit f n =
      directInitSchedule tm (f n) n ++
        (List.finRange (f n)).flatMap (tm.directStepFragment (f n) n) ++
        [numericAcceptanceGate (Fintype.card tm.Q)
          (stateIndex tm.toNTM tm.qhalt) (k + 2) (f n)
          (n + f n * directStepSize tm.toNTM (f n))] ++
        directPaddingSchedule (directOriginalRawGateCount tm (f n))
          (tm.directUnrollingGateBound f n) ++
        [directTerminalCopyGate n (directOriginalRawGateCount tm (f n))] := by
  simp only [TM.paddedDirectUnrollingRawCircuit]
  rw [directUnrollingRawCircuit_length_eq_original_internal]
  rw [tm.directUnrollingRawCircuit_eq_init_append_steps]
  rw [← directInitSchedule_eq_initFragment tm (f n) n hn]
  rw [numericAcceptanceGate_eq_acceptanceGate_internal]
  simp only [directPaddingSchedule, directTerminalCopyGate]

end Serializer

end CircuitUnrolling

end Complexity
