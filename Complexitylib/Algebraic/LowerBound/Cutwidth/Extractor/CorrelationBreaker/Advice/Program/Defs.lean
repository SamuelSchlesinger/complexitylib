/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Advice.Defs
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.FlipFlop.Program.Defs

/-!
# Total string evaluation of the advice chain

The loop retains both original sources, unary parameters, remaining advice,
and the current right state. A step consumes the first remaining advice bit;
after exhaustion it leaves the state unchanged. The initial right state is
zero-completed to its full width. The final depth-twenty-four call uses its
seed-width prefix and the original left source.

The evaluator input is `pair (pair x y) (pair scale (pair error advice))`.
The numerical parameters are lengths of their words. All operations are
total, including malformed pairings and invalid numerical parameters.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Extractor

open Complexity

/-- Every part of the advice-loop state, including the original source words. -/
structure AdviceRunState where
  /-- The original left source. -/
  x : List Bool
  /-- The original right source. -/
  y : List Bool
  /-- The common scale. -/
  scale : Nat
  /-- The common error exponent. -/
  error : Nat
  /-- Advice not yet consumed. -/
  remaining : List Bool
  /-- The current right state. -/
  q : List Bool

/-- The right-source prefix, padded with false bits to the full state width. -/
def adviceInitialWord (L : Nat) (y : List Bool) : List Bool :=
  (y ++ List.replicate (matchedBlockOutputBits 64 L) false).take
    (matchedBlockOutputBits 64 L)

/-- Initialize the loop with its full immutable input and remaining advice. -/
def adviceRunInitial (L e : Nat) (x y advice : List Bool) : AdviceRunState :=
  ⟨x, y, L, e, advice, adviceInitialWord L y⟩

/-- Consume the next advice bit, leaving the state fixed once the advice is empty. -/
def adviceRunStep (state : AdviceRunState) : AdviceRunState :=
  { state with
    remaining := state.remaining.drop 1
    q := if state.remaining.length = 0 then state.q else
      flipFlopStepRuntime state.scale state.error state.x state.y state.q
        (state.remaining[0]?.getD false) }

/-- Run exactly the requested number of advice transitions. -/
def adviceRun (L e : Nat) (x y advice : List Bool) (count : Nat) : AdviceRunState :=
  adviceRunStep^[count] (adviceRunInitial L e x y advice)

/-- Encode the full state, including the immutable source words and parameters. -/
def encodeAdviceRunState (state : AdviceRunState) : List Bool :=
  pair (pair state.x state.y) (pair (List.replicate state.scale true)
    (pair (List.replicate state.error true) (pair state.remaining state.q)))

/-- Total projections decode all parts of a state word. -/
def decodeAdviceRunState (z : List Bool) : AdviceRunState :=
  ⟨pairFst (pairFst z), pairSnd (pairFst z), (pairFst (pairSnd z)).length,
    (pairFst (pairSnd (pairSnd z))).length,
    pairFst (pairSnd (pairSnd (pairSnd z))), pairSnd (pairSnd (pairSnd (pairSnd z)))⟩

/-- A single encoded transition, total on arbitrary words. -/
def adviceRunStepEval (z : List Bool) : List Bool :=
  encodeAdviceRunState (adviceRunStep (decodeAdviceRunState z))

/-- Execute the advice chain, then extract from the original left source. -/
def adviceCorrelationBreakerRuntime (L e : Nat) (x y advice : List Bool) : List Bool :=
  matchedBlockExtractorRuntime 24 L e x
    ((adviceRun L e x y advice advice.length).q.take (matchedBlockSeedBits L))

/-- A single evaluator with unary scale/error words and arbitrary source/advice words. -/
def adviceCorrelationBreakerEval (z : List Bool) : List Bool :=
  adviceCorrelationBreakerRuntime (pairFst (pairSnd z)).length
    (pairFst (pairSnd (pairSnd z))).length
    (pairFst (pairFst z)) (pairSnd (pairFst z)) (pairSnd (pairSnd (pairSnd z)))

end Algebraic.Cutwidth.Extractor
