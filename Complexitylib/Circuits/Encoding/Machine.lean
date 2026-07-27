/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.Encoding.Machine.Defs
public import Complexitylib.Circuits.Encoding.Machine.Core
public import Complexitylib.Circuits.Encoding.Machine.Internal.FrontEnd
public import Complexitylib.Circuits.Encoding.Machine.GateStream
public import Complexitylib.Circuits.Encoding.Machine.NatCode
public import Complexitylib.Circuits.Encoding.Machine.RawGate

/-!
# Serialized circuit-evaluator machine

This module exposes the audited front end for a deterministic evaluator of
serialized circuit families. It validates the outer self-delimiting pair,
stages its code and input components on separate appendable work tapes, and
exposes the verified quadratic-time memoized evaluator from raw input through
its final verdict.

## Main results

- `pair_mem_circuitEvalLanguage_iff` identifies the target language on canonical
  paired inputs.
- `pairStageTM_hoareTime` gives the total staged-input contract in linear time.
- `Machine.evalFamilyCoreTM_hoareTime` gives the total staged-core contract in
  concrete quadratic time.
- `Machine.evalFamilyTM_decidesInTime` proves the complete evaluator decides
  `circuitEvalLanguage`, and `Machine.evalFamilyTime_bigO_quadratic` gives its
  polynomial bound.
- `Machine.emitNatCodeTM_hoareTimeSpace` emits terminated-unary natural codes
  from binary work tapes with reusable scratch and an all-prefix space bound.
- `Machine.emitRawGateTM_hoareTimeSpace` emits complete raw-gate codes from
  two preserved binary wire references.
- `Machine.emitRawGateStepTM_hoareTimeSpace` additionally advances the
  first-unused-wire counter after one emitted gate.
-/

@[expose] public section

namespace Complexity

namespace CircuitCode

/-- Membership in the evaluator language is successful Boolean evaluation. -/
@[simp] theorem mem_circuitEvalLanguage_iff (z : List Bool) :
    z ∈ circuitEvalLanguage ↔ evalFamilyPair? z = some true :=
  Iff.rfl

/-- A canonical outer pair belongs to the evaluator language exactly when its
tagged circuit code evaluates to true on the paired input. -/
theorem pair_mem_circuitEvalLanguage_iff (code input : List Bool) :
    pair code input ∈ circuitEvalLanguage ↔
      evalFamilyCode code input = some true := by
  simp [circuitEvalLanguage]

/-- Pairing a family's canonical member code with an input recognizes exactly
the language decided by that family. -/
theorem encodeAt_pair_mem_circuitEvalLanguage_iff
    (F : CircuitFamily Basis.andOr2) (input : List Bool) :
    pair (F.encodeAt input.length) input ∈ circuitEvalLanguage ↔
      F.evalList input = true := by
  simp [circuitEvalLanguage]

namespace Machine

/-- Every staged endpoint leaves the output at cell one with the canonical
left-marker invariant, ready for the evaluator core to overwrite its verdict. -/
theorem PairStagePost.outputReady {bits : List Bool} {inp : Tape}
    {work : Fin workTapeCount → Tape} {out : Tape}
    (h : PairStagePost bits inp work out) :
    out.StartInvariant ∧ out.head = 1 :=
  ⟨h.2.2.1, h.2.1⟩

/-- The pair-staging machine validates every outer input and, in linear time,
either rejects it without dirtying work tapes or exposes appendable code and
input prefixes for the evaluator core. -/
theorem pairStageTM_hoareTime (bits : List Bool) :
    pairStageTM.HoareTime (PairStagePre bits) (PairStagePost bits)
      (pairStageTime bits.length) :=
  Internal.pairStageTM_hoareTime_internal bits

end Machine

end CircuitCode

end Complexity
