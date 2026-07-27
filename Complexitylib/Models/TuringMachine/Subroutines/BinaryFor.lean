/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Models.TuringMachine.Subroutines.BinaryFor.Defs
public import Complexitylib.Models.TuringMachine.Subroutines.BinaryFor.Internal

/-!
# Canonical binary count-up loops

This module exposes an output-safe bounded loop whose counter and preserved
limit use canonical little-endian binary work tapes. Under the certified
invariant `counter ≤ limit`, every test scans the full limit width, so a
comparison has the value-independent exact time `2 * limit.size + 2`. A
nonterminal test runs the supplied body, increments the counter, and returns
to a fresh test; equality halts with both binary tapes rewound.

The generic certificates keep body-specific facts explicit. In particular,
the loop driver does not assume that an arbitrary body preserves its counter,
limit, or tape frames. Clients record those endpoint facts in
`BinaryForLoopSpec` and the corresponding prefix-space facts in
`BinaryForLoopSpaceSpec`.

## Main results

- `binaryForTM_compare_reachesIn_frame` gives the exact framed comparison.
- `BinaryForLoopSpec.reachesIn` composes a certified loop exactly.
- `BinaryForLoopSpaceSpec.prefix_withinAuxSpace` covers every run prefix.
- `IsTransducer.binaryForTM` preserves one-way output safety.
-/

@[expose] public section

namespace Complexity

namespace TM

variable {n : ℕ}

/-- At equality, one full-width comparison preserves every tape and reaches
the final driver configuration in exact time. -/
theorem binaryForTM_compare_reachesIn_frame_of_eq
    (body : TM n) (counterIdx limitIdx : Fin n)
    (hne : counterIdx ≠ limitIdx) (value : ℕ)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hcounter : (work₀ counterIdx).HasBinaryNat value)
    (hlimit : (work₀ limitIdx).HasBinaryNat value)
    (hinp : inp₀.read ≠ Γ.start)
    (hother : ∀ i, i ≠ counterIdx → i ≠ limitIdx →
      (work₀ i).read ≠ Γ.start)
    (hout : out₀.read ≠ Γ.start) :
    (binaryForTM body counterIdx limitIdx).reachesIn
      (binaryForCompareTime value)
      { state := .inl (.scan true)
        input := inp₀
        work := work₀
        output := out₀ }
      { state := .inl .done
        input := inp₀
        work := work₀
        output := out₀ } :=
  binaryForTM_compare_reachesIn_frame_of_eq_internal body counterIdx limitIdx
    hne value inp₀ work₀ out₀ hcounter hlimit hinp hother hout

/-- Strictly below the limit, one full-width comparison preserves every tape
and reaches the composite iteration start in exact time. -/
theorem binaryForTM_compare_reachesIn_frame_of_lt
    (body : TM n) (counterIdx limitIdx : Fin n)
    (hne : counterIdx ≠ limitIdx) (value limitValue : ℕ)
    (hlt : value < limitValue)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hcounter : (work₀ counterIdx).HasBinaryNat value)
    (hlimit : (work₀ limitIdx).HasBinaryNat limitValue)
    (hinp : inp₀.read ≠ Γ.start)
    (hother : ∀ i, i ≠ counterIdx → i ≠ limitIdx →
      (work₀ i).read ≠ Γ.start)
    (hout : out₀.read ≠ Γ.start) :
    (binaryForTM body counterIdx limitIdx).reachesIn
      (binaryForCompareTime limitValue)
      { state := .inl (.scan true)
        input := inp₀
        work := work₀
        output := out₀ }
      { state := .inr (binaryForIterationTM body counterIdx).qstart
        input := inp₀
        work := work₀
        output := out₀ } :=
  binaryForTM_compare_reachesIn_frame_of_lt_internal body counterIdx limitIdx
    hne value limitValue hlt inp₀ work₀ out₀ hcounter hlimit hinp hother hout

/-- A bounded canonical comparison has one exact, fully framed endpoint. It
enters the composite iteration exactly below the limit and halts exactly at
equality. -/
theorem binaryForTM_compare_reachesIn_frame
    (body : TM n) (counterIdx limitIdx : Fin n)
    (hne : counterIdx ≠ limitIdx) (value limitValue : ℕ)
    (hle : value ≤ limitValue)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hcounter : (work₀ counterIdx).HasBinaryNat value)
    (hlimit : (work₀ limitIdx).HasBinaryNat limitValue)
    (hinp : inp₀.read ≠ Γ.start)
    (hother : ∀ i, i ≠ counterIdx → i ≠ limitIdx →
      (work₀ i).read ≠ Γ.start)
    (hout : out₀.read ≠ Γ.start) :
    ∃ c',
      (binaryForTM body counterIdx limitIdx).reachesIn
        (binaryForCompareTime limitValue)
        { state := .inl (.scan true)
          input := inp₀
          work := work₀
          output := out₀ } c' ∧
      c'.input = inp₀ ∧
      c'.work = work₀ ∧
      c'.output = out₀ ∧
      (c'.state = .inr (binaryForIterationTM body counterIdx).qstart ↔
        value < limitValue) ∧
      (c'.state = .inl .done ↔ value = limitValue) :=
  binaryForTM_compare_reachesIn_frame_internal body counterIdx limitIdx hne
    value limitValue hle inp₀ work₀ out₀ hcounter hlimit hinp hother hout

/-- A certified count-up loop has its advertised exact remaining run. -/
theorem BinaryForLoopSpec.reachesIn {body : TM n}
    {counterIdx limitIdx : Fin n} {bodyTime : ℕ → ℕ} {limitValue : ℕ}
    (spec : BinaryForLoopSpec body counterIdx limitIdx bodyTime limitValue)
    (count value : ℕ) (hlimit : value + count = limitValue) :
    (binaryForTM body counterIdx limitIdx).reachesIn
      (binaryForLoopTime bodyTime limitValue value count)
      (spec.scanCfg value) spec.doneCfg :=
  spec.reachesIn_internal count value hlimit

/-- Every canonical scanner configuration in a certified range satisfies the
declared auxiliary-space budget. -/
theorem BinaryForLoopSpaceSpec.scanWithin
    {body : TM n} {counterIdx limitIdx : Fin n} {bodyTime : ℕ → ℕ}
    {limitValue inputLength spaceBound value : ℕ}
    {spec : BinaryForLoopSpec body counterIdx limitIdx bodyTime limitValue}
    (spaceSpec : BinaryForLoopSpaceSpec spec inputLength spaceBound)
    (hvalue : value ≤ limitValue) :
    (spec.scanCfg value).WithinAuxSpace inputLength spaceBound :=
  spaceSpec.scanWithin_internal hvalue

/-- The final configuration of a space-certified loop satisfies its declared
auxiliary-space budget. -/
theorem BinaryForLoopSpaceSpec.doneWithin
    {body : TM n} {counterIdx limitIdx : Fin n} {bodyTime : ℕ → ℕ}
    {limitValue inputLength spaceBound : ℕ}
    {spec : BinaryForLoopSpec body counterIdx limitIdx bodyTime limitValue}
    (spaceSpec : BinaryForLoopSpaceSpec spec inputLength spaceBound) :
    spec.doneCfg.WithinAuxSpace inputLength spaceBound :=
  spaceSpec.doneWithin_internal

/-- Every prefix of a certified binary count-up loop respects its declared
auxiliary-space budget. -/
theorem BinaryForLoopSpaceSpec.prefix_withinAuxSpace
    {body : TM n} {counterIdx limitIdx : Fin n} {bodyTime : ℕ → ℕ}
    {limitValue inputLength spaceBound : ℕ}
    {spec : BinaryForLoopSpec body counterIdx limitIdx bodyTime limitValue}
    (spaceSpec : BinaryForLoopSpaceSpec spec inputLength spaceBound)
    (count value t : ℕ) (c : Cfg n (binaryForTM body counterIdx limitIdx).Q)
    (hlimit : value + count = limitValue)
    (hreach : (binaryForTM body counterIdx limitIdx).reachesIn t
      (spec.scanCfg value) c)
    (htime : t ≤ binaryForLoopTime bodyTime limitValue value count) :
    c.WithinAuxSpace inputLength spaceBound :=
  spaceSpec.prefix_withinAuxSpace_internal count value t c hlimit hreach htime

/-- A binary count-up loop preserves the body's one-way-output discipline. -/
theorem IsTransducer.binaryForTM {body : TM n}
    (hbody : body.IsTransducer) (counterIdx limitIdx : Fin n) :
    (binaryForTM body counterIdx limitIdx).IsTransducer :=
  hbody.binaryForTM_internal counterIdx limitIdx

end TM

end Complexity
