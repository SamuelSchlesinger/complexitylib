/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.Program.Defs
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.Defs
public import Complexitylib.Classes.P.Defs
public import Complexitylib.Classes.P.Unary.Defs
public import Complexitylib.Tactic.PolyTime.Init
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.Program.Internal

/-!
# One uniform polynomial-time program for the complete affine construction

The selected program computes every parameter from the original input
lengths, a unary tampering count, and a unary target exponent. Canonical
inputs compute the actual first phase followed by all subset-doubling
rounds on the same original source words. The polynomial-time guarantee
covers every input, including malformed words and infeasible entropy
requests. Source and advice conditions belong to the statistical theorem.
-/

public section

namespace Algebraic.Cutwidth.Extractor

open Complexity

/-- The actual first phase and every subsequent runtime round match the semantic construction. -/
theorem affineCorrelationBreakerRuntime_eq (n d t L₀ e₀ L₁ e₁ er rounds : Nat)
    (first : MatchedBlockRuntimeValid n 64 L₀ e₀)
    (adviceGuard : FlipFlopSizeGuard d (matchedBlockOutputBits 64 L₀) L₁ e₁)
    (right : MatchedBlockRuntimeValid d 24 L₁ er)
    (rowGuard : MatchedBlockRuntimeValid
      (matchedBlockOutputBits (growingMatchedBlockDepth t) L₁) 24 L₁ er)
    (last : GrowingMatchedBlockRuntimeValid n t L₁ er)
    (x : Fin n → Bool) (y : Fin d → Bool) (advice : List Bool) :
    affineCorrelationBreakerRuntime t L₀ e₀ L₁ e₁ er rounds
      (List.ofFn x) (List.ofFn y) advice =
      List.ofFn (affineCorrelationBreaker n d (growingMatchedBlockDepth t)
        L₀ e₀ L₁ e₁ er rounds x y advice) :=
  Internal.affineCorrelationBreakerRuntime_eq n d t L₀ e₀ L₁ e₁ er rounds first adviceGuard right rowGuard last x y advice

/-- Every round has the same output width, including the zero-round initial phase. -/
theorem affineCorrelationBreakerRuntime_length (t L₀ e₀ L₁ e₁ er rounds : Nat)
    (x y advice : List Bool) :
    (affineCorrelationBreakerRuntime t L₀ e₀ L₁ e₁ er rounds x y advice).length =
      if GrowingMatchedBlockRuntimeValid x.length t L₁ er then
        2 ^ growingMatchedBlockDepth t * L₁ else 0 :=
  Internal.affineCorrelationBreakerRuntime_length t L₀ e₀ L₁ e₁ er rounds x y advice

/-- The complete runtime output is polynomially bounded even on invalid parameters. -/
theorem affineCorrelationBreakerRuntime_length_le (t L₀ e₀ L₁ e₁ er rounds : Nat)
    (x y advice : List Bool) :
    (affineCorrelationBreakerRuntime t L₀ e₀ L₁ e₁ er rounds x y advice).length ≤
      2 ^ 65 * (t + 1) * L₁ :=
  Internal.affineCorrelationBreakerRuntime_length_le t L₀ e₀ L₁ e₁ er rounds x y advice

/-- Actual initialization and a unary number of rounds form one uniform polynomial-time program. -/
@[polytime] theorem affineCorrelationBreakerRuntime_mem_FP {t L₀ e₀ L₁ e₁ er rounds : List Bool → Nat}
    {x y advice : List Bool → List Bool}
    (ht : UnaryFn t) (hL₀ : UnaryFn L₀) (he₀ : UnaryFn e₀)
    (hL₁ : UnaryFn L₁) (he₁ : UnaryFn e₁) (her : UnaryFn er) (hrounds : UnaryFn rounds)
    (hx : x ∈ FP) (hy : y ∈ FP) (hadvice : advice ∈ FP) :
    (fun z => affineCorrelationBreakerRuntime (t z) (L₀ z) (e₀ z) (L₁ z) (e₁ z) (er z)
      (rounds z) (x z) (y z) (advice z)) ∈ FP :=
  Internal.affineCorrelationBreakerRuntime_mem_FP ht hL₀ he₀ hL₁ he₁ her hrounds hx hy hadvice

/-- Every selected output has the prescribed growing-depth width. -/
theorem affineCorrelationBreakerSelectedRuntime_length (t target : Nat) (x y advice : List Bool) :
    (affineCorrelationBreakerSelectedRuntime t target x y advice).length =
      2 ^ growingMatchedBlockDepth t *
        affinePhaseOneScale x.length t advice.length (affineIterationTarget t target) :=
  Internal.affineCorrelationBreakerSelectedRuntime_length t target x y advice

/-- The selected width has a polynomial bound in the chooser inputs. -/
theorem affineCorrelationBreakerSelectedRuntime_length_le (t target : Nat)
    (x y advice : List Bool) :
    (affineCorrelationBreakerSelectedRuntime t target x y advice).length ≤
      2 ^ 65 * (t + 1) *
        affinePhaseOneScale x.length t advice.length (affineIterationTarget t target) :=
  Internal.affineCorrelationBreakerSelectedRuntime_length_le t target x y advice

/-- The selected total program computes the complete semantic construction with every guard discharged. -/
theorem affineCorrelationBreakerSelectedRuntime_eq (n t target : Nat) (advice : List Bool)
    (x : Fin n → Bool)
    (y : Fin (affinePhaseOneRightBits n t advice.length (affineIterationTarget t target)) → Bool) :
    affineCorrelationBreakerSelectedRuntime t target (List.ofFn x) (List.ofFn y) advice =
      List.ofFn (affineCorrelationBreakerSelected n t target advice x y) :=
  Internal.affineCorrelationBreakerSelectedRuntime_eq n t target advice x y

/-- Parameter computation, normalization, initialization, and all rounds are uniformly polynomial-time. -/
@[polytime] theorem affineCorrelationBreakerSelectedRuntime_mem_FP {t target : List Bool → Nat}
    {x y advice : List Bool → List Bool} (ht : UnaryFn t) (htarget : UnaryFn target)
    (hx : x ∈ FP) (hy : y ∈ FP) (hadvice : advice ∈ FP) :
    (fun z => affineCorrelationBreakerSelectedRuntime (t z) (target z)
      (x z) (y z) (advice z)) ∈ FP :=
  Internal.affineCorrelationBreakerSelectedRuntime_mem_FP ht htarget hx hy hadvice

/-- Decode three data words and the two unary parameters. -/
theorem affineCorrelationBreakerSelectedEval_pair (x y advice parameter targetWord : List Bool) :
    affineCorrelationBreakerSelectedEval
      (pair (pair x (pair y advice)) (pair parameter targetWord)) =
      affineCorrelationBreakerSelectedRuntime parameter.length targetWord.length x y advice :=
  Internal.affineCorrelationBreakerSelectedEval_pair x y advice parameter targetWord

/-- One paired evaluator serializes the entire selected semantic construction exactly. -/
theorem affineCorrelationBreakerSelectedEval_eq (n t target : Nat) (advice : List Bool)
    (x : Fin n → Bool)
    (y : Fin (affinePhaseOneRightBits n t advice.length (affineIterationTarget t target)) → Bool) :
    affineCorrelationBreakerSelectedEval (pair (pair (List.ofFn x) (pair (List.ofFn y) advice))
      (pair (List.replicate t true) (List.replicate target true))) =
      List.ofFn (affineCorrelationBreakerSelected n t target advice x y) :=
  Internal.affineCorrelationBreakerSelectedEval_eq n t target advice x y

/-- The single complete evaluator is polynomial-time on every encoded or malformed input. -/
@[polytime] theorem affineCorrelationBreakerSelectedEval_mem_FP : affineCorrelationBreakerSelectedEval ∈ FP :=
  Internal.affineCorrelationBreakerSelectedEval_mem_FP

end Algebraic.Cutwidth.Extractor
