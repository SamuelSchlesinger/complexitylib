/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Models.TuringMachine.Combinators.WorkBranch.Defs
public import Complexitylib.Models.TuringMachine.Experimental.BinaryRoutine.Defs
public import Complexitylib.Models.TuringMachine.Subroutines.BinaryFor.Defs

/-!
# Proof-carrying binary routine control -- definitions

This module adds value-level zero branching and canonical binary count-up
loops to `BinaryRoutine`.

The loop certificate here deliberately differs from `TM.BinaryForLoopSpec` in
two ways required by the routine interface. It starts at an arbitrary value,
so body obligations are restricted to the reachable segment, and it accepts
bounded iteration witnesses because `BinaryRoutine.Sound` advertises an upper
bound rather than an exact runtime. Comparisons and endpoints remain exact.
-/

@[expose] public section

namespace Complexity

namespace TM

/-- A bounded execution certificate for the reachable segment of a canonical
binary count-up loop.

Unlike `BinaryForLoopSpec`, iterations may finish before their advertised
bound and obligations below `startValue` are not requested. -/
structure BinaryForSegmentSpec {n : ℕ} (body : TM n)
    (counterIdx limitIdx : Fin n) (bodyTime : ℕ → ℕ)
    (startValue limitValue : ℕ) where
  /-- The counter and preserved-limit tapes are distinct. -/
  counter_ne_limit : counterIdx ≠ limitIdx
  /-- Canonical scanner configuration at each reachable counter value. -/
  scanCfg : ℕ → Cfg n (binaryForTM body counterIdx limitIdx).Q
  /-- Configuration at the composite body-plus-successor entry. -/
  iterationStartCfg : ℕ → Cfg n (binaryForTM body counterIdx limitIdx).Q
  /-- Configuration after the composite body-plus-successor iteration. -/
  iterationDoneCfg : ℕ → Cfg n (binaryForTM body counterIdx limitIdx).Q
  /-- Final halted driver configuration. -/
  doneCfg : Cfg n (binaryForTM body counterIdx limitIdx).Q
  /-- A nonterminal comparison enters the composite iteration exactly. -/
  testRun : ∀ value, startValue ≤ value → value < limitValue →
    (binaryForTM body counterIdx limitIdx).reachesIn
      (binaryForCompareTime limitValue) (scanCfg value)
      (iterationStartCfg value)
  /-- Selected actual runtime of each reachable composite iteration. -/
  iterationTime : ℕ → ℕ
  /-- The selected runtime stays within the advertised iteration bound. -/
  iterationTime_le : ∀ value, startValue ≤ value → value < limitValue →
    iterationTime value ≤ binaryForIterationTime bodyTime value
  /-- The composite iteration runs for its selected actual runtime. -/
  iterationRun : ∀ value, startValue ≤ value → value < limitValue →
    (binaryForTM body counterIdx limitIdx).reachesIn (iterationTime value)
      (iterationStartCfg value) (iterationDoneCfg value)
  /-- The preserving loopback seam starts the next comparison. -/
  loopbackStep : ∀ value, startValue ≤ value → value < limitValue →
    (binaryForTM body counterIdx limitIdx).step (iterationDoneCfg value) =
      some (scanCfg (value + 1))
  /-- Equality at the limit completes the final comparison exactly. -/
  doneRun :
    (binaryForTM body counterIdx limitIdx).reachesIn
      (binaryForCompareTime limitValue) (scanCfg limitValue) doneCfg
  /-- The supplied final driver configuration is genuinely halted. -/
  doneHalted : (binaryForTM body counterIdx limitIdx).halted doneCfg

/-- All-prefix auxiliary-space obligations for a bounded reachable loop
segment. -/
structure BinaryForSegmentSpaceSpec {n : ℕ} {body : TM n}
    {counterIdx limitIdx : Fin n} {bodyTime : ℕ → ℕ}
    {startValue limitValue : ℕ}
    (spec : BinaryForSegmentSpec body counterIdx limitIdx bodyTime
      startValue limitValue) (inputLength spaceBound : ℕ) where
  /-- Every reachable comparison prefix stays inside the shared budget. -/
  testPrefixWithin : ∀ value time cfg, startValue ≤ value →
    value ≤ limitValue → time ≤ binaryForCompareTime limitValue →
    (binaryForTM body counterIdx limitIdx).reachesIn time
      (spec.scanCfg value) cfg →
    cfg.WithinAuxSpace inputLength spaceBound
  /-- Every reachable composite-iteration prefix stays inside the budget. -/
  iterationPrefixWithin : ∀ value time cfg, startValue ≤ value →
    value < limitValue → time ≤ spec.iterationTime value →
    (binaryForTM body counterIdx limitIdx).reachesIn time
      (spec.iterationStartCfg value) cfg →
    cfg.WithinAuxSpace inputLength spaceBound

end TM

namespace BinaryRoutine

/-- Select between two routines by whether a canonical binary work value is
zero. The blank branch is the zero branch. -/
def branchZero (idx : Fin n) (onZero onPositive : BinaryRoutine n) :
    BinaryRoutine n where
  machine := TM.branchWorkBlankTM idx onZero.machine onPositive.machine
  requires := fun values =>
    if values idx = 0 then onZero.requires values
    else onPositive.requires values
  effect := fun values =>
    if values idx = 0 then onZero.effect values
    else onPositive.effect values
  emitted := fun values =>
    if values idx = 0 then onZero.emitted values
    else onPositive.emitted values
  timeBound := fun values =>
    TM.branchWorkBlankTime (onZero.timeBound values)
      (onPositive.timeBound values)
  spaceBound := fun initialSpace values =>
    max (onZero.spaceBound initialSpace values)
      (onPositive.spaceBound initialSpace values)

/-- One pure count-up iteration: apply the body effect, then overwrite the
preserved counter with its successor. -/
def binaryForStep (body : BinaryRoutine n) (counterIdx : Fin n)
    (values : BinaryValues n) : BinaryValues n :=
  Function.update (body.effect values) counterIdx (values counterIdx + 1)

/-- Pure work-vector trajectory after a number of count-up iterations. -/
def binaryForValues (body : BinaryRoutine n) (counterIdx : Fin n)
    (initial : BinaryValues n) : ℕ → BinaryValues n
  | 0 => initial
  | count + 1 =>
      binaryForStep body counterIdx
        (binaryForValues body counterIdx initial count)

/-- Word emitted by the first `count` iterations of a count-up body. -/
def binaryForEmitted (body : BinaryRoutine n) (counterIdx : Fin n)
    (initial : BinaryValues n) : ℕ → List Bool
  | 0 => []
  | count + 1 =>
      binaryForEmitted body counterIdx initial count ++
        body.emitted (binaryForValues body counterIdx initial count)

/-- Body-time bound at an absolute counter value in a pure trajectory. -/
def binaryForBodyTime (body : BinaryRoutine n) (counterIdx : Fin n)
    (initial : BinaryValues n) (startValue value : ℕ) : ℕ :=
  body.timeBound
    (binaryForValues body counterIdx initial (value - startValue))

/-- Number of iterations remaining between the initial counter and limit. -/
def binaryForCount (counterIdx limitIdx : Fin n)
    (values : BinaryValues n) : ℕ :=
  values limitIdx - values counterIdx

/-- Advertised upper bound for a proof-carrying binary count-up loop. -/
def binaryForTime (body : BinaryRoutine n) (counterIdx limitIdx : Fin n)
    (values : BinaryValues n) : ℕ :=
  TM.binaryForLoopTime
    (binaryForBodyTime body counterIdx values (values counterIdx))
    (values limitIdx) (values counterIdx)
    (binaryForCount counterIdx limitIdx values)

/-- Space needed by one body-plus-successor iteration. This is a maximum,
not a sum: sequential phases reuse the same work cells. -/
def binaryForIterationSpace (body : BinaryRoutine n) (counterIdx : Fin n)
    (initialSpace : ℕ) (initial : BinaryValues n) (count : ℕ) : ℕ :=
  let current := binaryForValues body counterIdx initial count
  max (body.spaceBound initialSpace current)
    (initialSpace + TM.binarySuccTime (current counterIdx))

/-- Maximum space of the first `count` iterations. -/
def binaryForIterationSpaceMax (body : BinaryRoutine n)
    (counterIdx : Fin n) (initialSpace : ℕ)
    (initial : BinaryValues n) : ℕ → ℕ
  | 0 => initialSpace
  | count + 1 =>
      max (binaryForIterationSpaceMax body counterIdx initialSpace initial count)
        (binaryForIterationSpace body counterIdx initialSpace initial count)

/-- Reusable auxiliary-space bound for a binary count-up loop. Comparison
width and per-iteration requirements are maximized, so the number of
iterations does not itself consume space. -/
def binaryForSpace (body : BinaryRoutine n) (counterIdx limitIdx : Fin n)
    (initialSpace : ℕ) (values : BinaryValues n) : ℕ :=
  max (initialSpace + TM.binaryForCompareTime (values limitIdx))
    (binaryForIterationSpaceMax body counterIdx initialSpace values
      (binaryForCount counterIdx limitIdx values))

/-- Iterate `body` while a canonical binary counter is strictly below a
preserved canonical limit, incrementing the counter after every body run.

The domain honestly requires the body at every reachable intermediate value
and requires its pure effect to preserve both controller values. -/
def binaryFor (body : BinaryRoutine n) (counterIdx limitIdx : Fin n) :
    BinaryRoutine n where
  machine := TM.binaryForTM body.machine counterIdx limitIdx
  requires := fun values =>
    counterIdx ≠ limitIdx ∧ values counterIdx ≤ values limitIdx ∧
      ∀ count, count < binaryForCount counterIdx limitIdx values →
        let current := binaryForValues body counterIdx values count
        body.requires current ∧
          body.effect current counterIdx = current counterIdx ∧
          body.effect current limitIdx = current limitIdx
  effect := fun values =>
    binaryForValues body counterIdx values
      (binaryForCount counterIdx limitIdx values)
  emitted := fun values =>
    binaryForEmitted body counterIdx values
      (binaryForCount counterIdx limitIdx values)
  timeBound := binaryForTime body counterIdx limitIdx
  spaceBound := binaryForSpace body counterIdx limitIdx

end BinaryRoutine

end Complexity
