/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Models.TuringMachine.OutputProbe.Defs
import Complexitylib.Models.TuringMachine.Subroutines.BlankWorkPrefixMany.Defs

/-!
# Restartable output-probe cleanup -- definitions

The retargeted probe owns `n` source scratch tapes, one query countdown, and
one captured-bit tape. Cleanup adds one reusable zero counter and one preserved
binary limit, rewinds the input, and blanks every probe-owned tape.
-/

namespace Complexity

namespace TM

/-- Syntactic work-tape arity of a retargeted `n`-tape probe placed before its
two cleanup tapes. This expression is propositionally equal to `n + 4`; its
placement-normal form avoids casts in controller compositions. -/
abbrev outputProbeControllerTapes (n : ℕ) : ℕ :=
  0 + (n + 1 + 1) + 2

/-- Embed one source work index in the full cleanup frame. -/
def outputProbeCleanupSourceIdx {n : ℕ} (idx : Fin n) :
    Fin (outputProbeControllerTapes n) :=
  ⟨idx, by dsimp only [outputProbeControllerTapes]; omega⟩

/-- Physical query-countdown index. -/
def outputProbeCleanupCountdownIdx (n : ℕ) :
    Fin (outputProbeControllerTapes n) :=
  ⟨n, by dsimp only [outputProbeControllerTapes]; omega⟩

/-- Physical captured-bit index. -/
def outputProbeCleanupCaptureIdx (n : ℕ) :
    Fin (outputProbeControllerTapes n) :=
  ⟨n + 1, by dsimp only [outputProbeControllerTapes]; omega⟩

/-- Reusable zero counter used by sparse-prefix cleanup. -/
def outputProbeCleanupCounterIdx (n : ℕ) :
    Fin (outputProbeControllerTapes n) :=
  ⟨n + 2, by dsimp only [outputProbeControllerTapes]; omega⟩

/-- Preserved binary cleanup limit. -/
def outputProbeCleanupLimitIdx (n : ℕ) :
    Fin (outputProbeControllerTapes n) :=
  ⟨n + 3, by dsimp only [outputProbeControllerTapes]; omega⟩

/-- Source scratch tapes followed by the countdown and captured-bit tapes. -/
def outputProbeCleanupTargets (n : ℕ) :
    List (Fin (outputProbeControllerTapes n)) :=
  List.ofFn outputProbeCleanupSourceIdx ++
    [outputProbeCleanupCountdownIdx n, outputProbeCleanupCaptureIdx n]

/-- Literal input tape after rewinding to the first ordinary cell. -/
def outputProbeRewoundInput (tape : Tape) : Tape where
  head := 1
  cells := tape.cells

/-- Rewind the shared input, then reset every dirty probe-owned work tape. -/
def outputProbeCleanupTM (n : ℕ) : TM (outputProbeControllerTapes n) :=
  seqTM rewindInputTM
    (rewindBlankWorkPrefixManyTM (outputProbeCleanupCounterIdx n)
      (outputProbeCleanupLimitIdx n) (outputProbeCleanupTargets n))

/-- Exact cleanup runtime. -/
def outputProbeCleanupTime (n inputHeadBound limit : ℕ)
    (headBound : Fin (outputProbeControllerTapes n) → ℕ) : ℕ :=
  inputHeadBound + 2 + 1 +
    rewindBlankWorkPrefixManyTime headBound limit
      (outputProbeCleanupTargets n)

/-- All-prefix cleanup space envelope. -/
def outputProbeCleanupSpace (n initialSpace limit : ℕ)
    (headBound : Fin (outputProbeControllerTapes n) → ℕ) : ℕ :=
  max initialSpace
    (rewindBlankWorkPrefixManySpace initialSpace headBound limit
      (outputProbeCleanupTargets n))

end TM

end Complexity
