/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Classes.PPoly.Uniform.Unrolling.Serializer.Finalization.Defs
public import Complexitylib.Classes.PPoly.Uniform.Unrolling.Serializer.Finalization.Internal

/-!
# Numeric finalization schedule for direct tableau serialization

This module exposes a natural-number acceptance gate, exact padding and
terminal-copy phase laws, and the complete literal decomposition of every
normalized positive padded direct-unrolling circuit. Together with the numeric
initialization schedule and canonical transition fragments, the decomposition
specifies the raw gate stream without run-time configuration atoms or formulas.

## Main results

- `numericAcceptanceGate_eq_acceptanceGate` identifies the arithmetic gate.
- `directUnrollingRawCircuit_length_eq_original` gives the exact unpadded count.
- `paddedDirectUnrollingRawCircuit_eq_numericSchedule` gives the complete raw
  list decomposition.
-/

@[expose] public section

namespace Complexity

namespace CircuitUnrolling

namespace Serializer

/-- The numeric state/output-cell addresses literally produce the existing
acceptance gate for the fixed deterministic machine. -/
theorem numericAcceptanceGate_eq_acceptanceGate (tm : TM k)
    (T finalConfigBase : ℕ) :
    numericAcceptanceGate (Fintype.card tm.Q)
        (stateIndex tm.toNTM tm.qhalt) (k + 2) T finalConfigBase =
      acceptanceGate tm.toNTM T finalConfigBase :=
  numericAcceptanceGate_eq_acceptanceGate_internal tm T finalConfigBase

/-- The numeric padding phase contains exactly the closed-bound shortfall. -/
@[simp] theorem length_directPaddingSchedule
    (originalRawGateCount closedBound : ℕ) :
    (directPaddingSchedule originalRawGateCount closedBound).length =
      closedBound - originalRawGateCount :=
  length_directPaddingSchedule_internal originalRawGateCount closedBound

/-- Every index in the numeric padding phase emits a dead constant-false gate. -/
theorem getElem_directPaddingSchedule
    (originalRawGateCount closedBound : ℕ)
    (index : Fin (closedBound - originalRawGateCount)) :
    (directPaddingSchedule originalRawGateCount closedBound)[index.val]'(by
      rw [length_directPaddingSchedule]
      exact index.isLt) = CircuitCode.RawGate.constant 0 false :=
  getElem_directPaddingSchedule_internal originalRawGateCount closedBound index

/-- Padding followed by the terminal copy has shortfall-plus-one gates. -/
@[simp] theorem length_directFinalizationSuffix
    (n originalRawGateCount closedBound : ℕ) :
    (directFinalizationSuffix n originalRawGateCount closedBound).length =
      closedBound - originalRawGateCount + 1 :=
  length_directFinalizationSuffix_internal n originalRawGateCount closedBound

/-- Indices before the finalization boundary are exactly the padding phase. -/
theorem getElem_directFinalizationSuffix_padding
    (n originalRawGateCount closedBound : ℕ)
    (index : Fin (closedBound - originalRawGateCount)) :
    (directFinalizationSuffix n originalRawGateCount closedBound)[index.val]'(by
      rw [length_directFinalizationSuffix]
      omega) = CircuitCode.RawGate.constant 0 false :=
  getElem_directFinalizationSuffix_padding_internal n originalRawGateCount
    closedBound index

/-- The gate at the finalization boundary is the terminal original-output copy. -/
theorem getElem_directFinalizationSuffix_terminal
    (n originalRawGateCount closedBound : ℕ) :
    (directFinalizationSuffix n originalRawGateCount closedBound)[
        closedBound - originalRawGateCount]'(by
          rw [length_directFinalizationSuffix]
          omega) = directTerminalCopyGate n originalRawGateCount :=
  getElem_directFinalizationSuffix_terminal_internal n originalRawGateCount
    closedBound

/-- Every canonical deterministic transition fragment has the fixed numeric
layer size. -/
@[simp] theorem directStepFragment_length (tm : TM k) (T n : ℕ)
    (index : Fin T) :
    (tm.directStepFragment T n index).length = directStepSize tm.toNTM T :=
  directStepFragment_length_internal tm T n index

/-- The unpadded raw tableau has one initial block, `T` equal transition
fragments, and one acceptance gate. -/
@[simp] theorem directUnrollingRawCircuit_length_eq_original
    (tm : TM k) (f : ℕ → ℕ) (n : ℕ) [NeZero n] :
    (tm.directUnrollingRawCircuit f n).length =
      directOriginalRawGateCount tm (f n) :=
  directUnrollingRawCircuit_length_eq_original_internal tm f n

/-- A normalized positive padded direct tableau is literally numeric
initialization, canonical transition fragments, numeric acceptance, dead
padding, and one terminal copy of the original acceptance output. -/
theorem paddedDirectUnrollingRawCircuit_eq_numericSchedule
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
        [directTerminalCopyGate n (directOriginalRawGateCount tm (f n))] :=
  paddedDirectUnrollingRawCircuit_eq_numericSchedule_internal tm f n hn

end Serializer

end CircuitUnrolling

end Complexity
