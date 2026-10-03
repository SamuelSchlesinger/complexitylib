/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Advice.Program.Defs
public import Complexitylib.Classes.P.Unary.Defs
public import Complexitylib.Classes.P.Defs
public import Complexitylib.Tactic.PolyTime.Init
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Advice.Program.Internal
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Advice.Program.Internal.Run

/-!
# Correct and uniform polynomial-time evaluation of the full advice chain

The actual left-to-right advice fold and final extraction agree with their
Boolean-vector definitions at the common scale. A single total string
program handles variable sources, scale, error, and advice length. Its loop
bound includes both original sources, both parameters, remaining advice,
and the right state. No validity promise is needed for polynomial time.

These results establish the algorithm and its runtime. The statistical
chain invariant and a correlation-breaking guarantee remain separate.
-/

public section

namespace Algebraic.Cutwidth.Extractor

open Complexity

/-- Initialization always writes the whole right-state width, using false completion. -/
theorem adviceInitialWord_length (L : Nat) (y : List Bool) :
    (adviceInitialWord L y).length = matchedBlockOutputBits 64 L :=
  Internal.adviceInitialWord_length L y

/-- Runtime initialization exactly serializes the semantic prefix with false completion. -/
theorem adviceInitialState_ofFn (m L : Nat) (y : Fin m → Bool) :
    List.ofFn (adviceInitialState m L y) = adviceInitialWord L (List.ofFn y) :=
  Internal.adviceInitialState_ofFn m L y

/-- The full state codec has this exact length, including its immutable data. -/
theorem encodeAdviceRunState_length (state : AdviceRunState) :
    (encodeAdviceRunState state).length =
      4 * state.x.length + 2 * state.y.length + 2 * state.scale + 2 * state.error +
        2 * state.remaining.length + state.q.length + 12 :=
  Internal.encodeAdviceRunState_length state

/-- Encoding and decoding preserve every component of a canonical state. -/
theorem decodeAdviceRunState_encode (state : AdviceRunState) :
    decodeAdviceRunState (encodeAdviceRunState state) = state :=
  Internal.decodeAdviceRunState_encode state

/-- The encoded transition computes exactly the structured transition. -/
theorem adviceRunStepEval_encode (state : AdviceRunState) :
    adviceRunStepEval (encodeAdviceRunState state) =
      encodeAdviceRunState (adviceRunStep state) :=
  Internal.adviceRunStepEval_encode state

/-- Every iterate has a bound accounting for the entire encoded state. -/
theorem adviceRun_length_le (L e : Nat) (x y advice : List Bool) (i : Nat) :
    (encodeAdviceRunState (adviceRun L e x y advice i)).length ≤
      4 * x.length + 2 * y.length + 2 * L + 2 * e + 2 * advice.length +
        matchedBlockOutputBits 64 L + 12 :=
  Internal.adviceRun_length_le L e x y advice i

/-- Canonical execution consumes all advice and writes exactly the semantic final state. -/
theorem adviceRun_eq_adviceFold (n m L e : Nat) (guard : FlipFlopSizeGuard n m L e)
    (x : Fin n → Bool) (y : Fin m → Bool) (advice : List Bool) :
    adviceRun L e (List.ofFn x) (List.ofFn y) advice advice.length =
      ⟨List.ofFn x, List.ofFn y, L, e, [],
        List.ofFn (adviceFold n m L e x y (adviceInitialState m L y) advice)⟩ :=
  Internal.adviceRun_eq_adviceFold n m L e guard x y advice

/-- The complete runtime agrees with the actual advice chain and final extractor. -/
theorem adviceCorrelationBreakerRuntime_eq (n m L e : Nat)
    (guard : FlipFlopSizeGuard n m L e) (x : Fin n → Bool) (y : Fin m → Bool)
    (advice : List Bool) :
    adviceCorrelationBreakerRuntime L e (List.ofFn x) (List.ofFn y) advice =
      List.ofFn (adviceCorrelationBreaker n m L e x y advice) :=
  Internal.adviceCorrelationBreakerRuntime_eq n m L e guard x y advice

/-- Every result fits in the common seed width, including invalid inputs. -/
theorem adviceCorrelationBreakerRuntime_length_le (L e : Nat) (x y advice : List Bool) :
    (adviceCorrelationBreakerRuntime L e x y advice).length ≤ matchedBlockSeedBits L :=
  Internal.adviceCorrelationBreakerRuntime_length_le L e x y advice

/-- The total encoded step is polynomial-time on arbitrary state words. -/
@[polytime] theorem adviceRunStepEval_mem_FP : adviceRunStepEval ∈ FP :=
  Internal.adviceRunStepEval_mem_FP

/-- The complete bounded loop is uniform in both parameters and all three input words. -/
@[polytime] theorem adviceRun_encoded_mem_FP {L e : List Bool → Nat}
    {x y advice : List Bool → List Bool} (hL : UnaryFn L) (he : UnaryFn e)
    (hx : x ∈ FP) (hy : y ∈ FP) (hadvice : advice ∈ FP) :
    (fun z => encodeAdviceRunState
      (adviceRun (L z) (e z) (x z) (y z) (advice z) (advice z).length)) ∈ FP :=
  Internal.adviceRun_encoded_mem_FP hL he hx hy hadvice

/-- All advice steps and final extraction have one unconditional polynomial-time certificate. -/
@[polytime] theorem adviceCorrelationBreakerRuntime_mem_FP {L e : List Bool → Nat}
    {x y advice : List Bool → List Bool} (hL : UnaryFn L) (he : UnaryFn e)
    (hx : x ∈ FP) (hy : y ∈ FP) (hadvice : advice ∈ FP) :
    (fun z => adviceCorrelationBreakerRuntime (L z) (e z) (x z) (y z) (advice z)) ∈ FP :=
  Internal.adviceCorrelationBreakerRuntime_mem_FP hL he hx hy hadvice

/-- The evaluator decodes original sources, unary scale/error, and the whole advice word. -/
theorem adviceCorrelationBreakerEval_pair (x y scale error advice : List Bool) :
    adviceCorrelationBreakerEval (pair (pair x y) (pair scale (pair error advice))) =
      adviceCorrelationBreakerRuntime scale.length error.length x y advice :=
  Internal.adviceCorrelationBreakerEval_pair x y scale error advice

/-- One total string evaluator computes the full advice construction in polynomial time. -/
@[polytime] theorem adviceCorrelationBreakerEval_mem_FP : adviceCorrelationBreakerEval ∈ FP :=
  Internal.adviceCorrelationBreakerEval_mem_FP

end Algebraic.Cutwidth.Extractor
