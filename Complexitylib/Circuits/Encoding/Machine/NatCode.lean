/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.Encoding.Machine.NatCode.Defs
public import Complexitylib.Circuits.Encoding.Machine.NatCode.Internal

/-!
# Machine emission of terminated-unary natural codes

This module exposes a concrete consumer of the canonical binary count-up loop.
Starting with a zero scratch counter and a distinct preserved binary limit, the
machine emits one `true` bit per value below the limit, clears the scratch tape
back to canonical zero, and emits the terminating `false` bit.

The endpoint contracts preserve the complete input and work-tape frame and
append exactly `NatCode.encode value`. The space contract covers every
reachable configuration; output growth is uncharged because the machine also
satisfies the one-way-output transducer discipline.

## Main results

- `emitNatCodeLoopTM_reachesIn_frame` gives the exact unary-body loop run.
- `emitNatCodeTM_hoareTime` gives the restored-frame endpoint and time bound.
- `emitNatCodeTM_hoareTimeSpace` adds an all-prefix auxiliary-space bound.
- `emitNatCodeTM_isTransducer` proves one-way-output safety.
-/

@[expose] public section

namespace Complexity

namespace CircuitCode

namespace Machine

open TM

variable {n : ℕ}

/-- The unary-body loop has an exact runtime and endpoint: it preserves the
input and every nonscratch work tape, leaves the scratch counter equal to the
limit, and appends exactly `value` one-bits. -/
theorem emitNatCodeLoopTM_reachesIn_frame
    (counterIdx limitIdx : Fin n) (hne : counterIdx ≠ limitIdx)
    (value : ℕ) (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (ys : List Bool) (hinp : Parked inp₀)
    (hcounter : (work₀ counterIdx).HasBinaryNat 0)
    (hlimit : (work₀ limitIdx).HasBinaryNat value)
    (hother : ∀ i, i ≠ counterIdx → i ≠ limitIdx → Parked (work₀ i))
    (hout : OutAcc ys out₀) :
    ∃ c',
      (emitNatCodeLoopTM counterIdx limitIdx).reachesIn
        (emitNatCodeLoopTime value)
        { state := (emitNatCodeLoopTM counterIdx limitIdx).qstart
          input := inp₀
          work := work₀
          output := out₀ } c' ∧
      (emitNatCodeLoopTM counterIdx limitIdx).halted c' ∧
      c'.input = inp₀ ∧
      c'.work = Function.update work₀ counterIdx
        ((Tape.init (value.bits.map Γ.ofBool)).move Dir3.right) ∧
      OutAcc (ys ++ List.replicate value true) c'.output :=
  emitNatCodeLoopTM_reachesIn_endpoint_internal counterIdx limitIdx hne value
    inp₀ work₀ out₀ ys hinp hcounter hlimit hother hout

/-- Terminated-unary emission restores the scratch counter and the complete
external frame, then appends exactly `NatCode.encode value` within
`emitNatCodeTime value` steps. -/
theorem emitNatCodeTM_hoareTime
    (counterIdx limitIdx : Fin n) (hne : counterIdx ≠ limitIdx)
    (value : ℕ) (inp₀ : Tape) (work₀ : Fin n → Tape) (ys : List Bool)
    (hinp : Parked inp₀)
    (hcounter : (work₀ counterIdx).HasBinaryNat 0)
    (hlimit : (work₀ limitIdx).HasBinaryNat value)
    (hother : ∀ i, i ≠ counterIdx → i ≠ limitIdx → Parked (work₀ i)) :
    (emitNatCodeTM counterIdx limitIdx).HoareTime
      (EmitPred inp₀ work₀ ys)
      (EmitPred inp₀ work₀ (ys ++ NatCode.encode value))
      (emitNatCodeTime value) :=
  emitNatCodeTM_hoareTime_internal counterIdx limitIdx hne value inp₀ work₀
    ys hinp hcounter hlimit hother

/-- Time-and-space form of `emitNatCodeTM_hoareTime`. The hypotheses state
that the initial input/work heads fit in `initialSpace`; every reachable
configuration then fits in `emitNatCodeSpace initialSpace value`. -/
theorem emitNatCodeTM_hoareTimeSpace
    (counterIdx limitIdx : Fin n) (hne : counterIdx ≠ limitIdx)
    (value inputLength initialSpace : ℕ)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (ys : List Bool)
    (hinp : Parked inp₀)
    (hcounter : (work₀ counterIdx).HasBinaryNat 0)
    (hlimit : (work₀ limitIdx).HasBinaryNat value)
    (hother : ∀ i, i ≠ counterIdx → i ≠ limitIdx → Parked (work₀ i))
    (hworkSpace : ∀ i, (work₀ i).head ≤ initialSpace)
    (hinputSpace : inp₀.head ≤ inputLength + initialSpace + 1) :
    (emitNatCodeTM counterIdx limitIdx).HoareTimeSpace
      (EmitPred inp₀ work₀ ys)
      (EmitPred inp₀ work₀ (ys ++ NatCode.encode value))
      (emitNatCodeTime value) inputLength
      (emitNatCodeSpace initialSpace value) :=
  emitNatCodeTM_hoareTimeSpace_internal counterIdx limitIdx hne value inputLength
    initialSpace inp₀ work₀ ys hinp hcounter hlimit hother hworkSpace
    hinputSpace

/-- Natural-code emission never moves its output head left. -/
theorem emitNatCodeTM_isTransducer (counterIdx limitIdx : Fin n) :
    (emitNatCodeTM counterIdx limitIdx).IsTransducer :=
  emitNatCodeTM_isTransducer_internal counterIdx limitIdx

end Machine

end CircuitCode

end Complexity
