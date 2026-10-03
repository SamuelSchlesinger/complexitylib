/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.PhaseOne.Program.Defs
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.PhaseOne.Defs
public import Complexitylib.Classes.P.Defs
public import Complexitylib.Classes.P.Unary.Defs
public import Complexitylib.Tactic.PolyTime.Init
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.PhaseOne.Program.Internal

/-!
# Uniform computation of the actual first affine phase

One total string program performs the first extraction, the actual advice
construction, and the growing-depth final extraction, retaining the original
source words throughout. Canonical inputs agree with `affinePhaseOneOutput`
under the three explicit component guards. No source distribution or
statistical premise occurs in the computation theorem.

The runtime and paired evaluator are uniformly polynomial-time on all
inputs. In particular, the unary parameter selects logarithmic recursion
depth; arbitrary unary depths with exponentially many leaves are not used.
-/

public section

namespace Algebraic.Cutwidth.Extractor

/-- False completion produces exactly the first matched seed width. -/
theorem affinePhaseOneFirstSeedWord_length (L₀ : Nat) (y : List Bool) :
    (affinePhaseOneFirstSeedWord L₀ y).length = matchedBlockSeedBits L₀ :=
  Internal.affinePhaseOneFirstSeedWord_length L₀ y

/-- The total prefix operation agrees with the semantic initial seed, including short words. -/
theorem affinePhaseOneFirstSeed_ofFn (d L₀ : Nat) (y : Fin d → Bool) :
    List.ofFn (affinePhaseOneFirstSeed d L₀ y) =
      affinePhaseOneFirstSeedWord L₀ (List.ofFn y) :=
  Internal.affinePhaseOneFirstSeed_ofFn d L₀ y

/-- The three actual string calls compute the semantic first-phase output exactly. -/
theorem affinePhaseOneRuntime_eq_affinePhaseOneOutput (n d t L₀ e₀ L₁ e₁ er : Nat)
    (first : MatchedBlockRuntimeValid n 64 L₀ e₀)
    (adviceGuard : FlipFlopSizeGuard d (matchedBlockOutputBits 64 L₀) L₁ e₁)
    (last : GrowingMatchedBlockRuntimeValid n t L₁ er)
    (x : Fin n → Bool) (y : Fin d → Bool) (advice : List Bool) :
    affinePhaseOneRuntime t L₀ e₀ L₁ e₁ er (List.ofFn x) (List.ofFn y) advice =
      List.ofFn (affinePhaseOneOutput n d (growingMatchedBlockDepth t)
        L₀ e₀ L₁ e₁ er x y advice) :=
  Internal.affinePhaseOneRuntime_eq_affinePhaseOneOutput n d t L₀ e₀ L₁ e₁ er
    first adviceGuard last x y advice

/-- Exact output length depends only on the final component's guard. -/
theorem affinePhaseOneRuntime_length (t L₀ e₀ L₁ e₁ er : Nat) (x y advice : List Bool) :
    (affinePhaseOneRuntime t L₀ e₀ L₁ e₁ er x y advice).length =
      if GrowingMatchedBlockRuntimeValid x.length t L₁ er then
        2 ^ growingMatchedBlockDepth t * L₁ else 0 :=
  Internal.affinePhaseOneRuntime_length t L₀ e₀ L₁ e₁ er x y advice

/-- A polynomial output bound holds for every choice of parameters and source words. -/
theorem affinePhaseOneRuntime_length_le (t L₀ e₀ L₁ e₁ er : Nat) (x y advice : List Bool) :
    (affinePhaseOneRuntime t L₀ e₀ L₁ e₁ er x y advice).length ≤ 2 ^ 65 * (t + 1) * L₁ :=
  Internal.affinePhaseOneRuntime_length_le t L₀ e₀ L₁ e₁ er x y advice

open Complexity in
/-- Exact initial-seed padding is uniformly polynomial-time. -/
@[polytime] theorem affinePhaseOneFirstSeedWord_mem_FP {L₀ : List Bool → Nat}
    {y : List Bool → List Bool} (hL₀ : UnaryFn L₀) (hy : y ∈ FP) :
    (fun z => affinePhaseOneFirstSeedWord (L₀ z) (y z)) ∈ FP :=
  Internal.affinePhaseOneFirstSeedWord_mem_FP hL₀ hy

open Complexity in
/-- All numerical and word operands may vary with the runtime input. -/
@[polytime] theorem affinePhaseOneRuntime_mem_FP {t L₀ e₀ L₁ e₁ er : List Bool → Nat}
    {x y advice : List Bool → List Bool}
    (ht : UnaryFn t) (hL₀ : UnaryFn L₀) (he₀ : UnaryFn e₀)
    (hL₁ : UnaryFn L₁) (he₁ : UnaryFn e₁) (her : UnaryFn er)
    (hx : x ∈ FP) (hy : y ∈ FP) (hadvice : advice ∈ FP) :
    (fun z => affinePhaseOneRuntime (t z) (L₀ z) (e₀ z) (L₁ z) (e₁ z) (er z)
      (x z) (y z) (advice z)) ∈ FP :=
  Internal.affinePhaseOneRuntime_mem_FP ht hL₀ he₀ hL₁ he₁ her hx hy hadvice

open Complexity in
/-- The paired evaluator decodes three data words and six unary numerical words. -/
theorem affinePhaseOneEval_pair (x y advice parameter firstScale firstError
    secondScale secondError finalError : List Bool) :
    affinePhaseOneEval (pair (pair x (pair y advice))
      (pair parameter (pair (pair firstScale firstError)
        (pair secondScale (pair secondError finalError))))) =
      affinePhaseOneRuntime parameter.length firstScale.length firstError.length
        secondScale.length secondError.length finalError.length x y advice :=
  Internal.affinePhaseOneEval_pair x y advice parameter firstScale firstError
    secondScale secondError finalError

open Complexity in
/-- One paired evaluator is polynomial-time on all strings, including malformed pairings. -/
@[polytime] theorem affinePhaseOneEval_mem_FP : affinePhaseOneEval ∈ FP :=
  Internal.affinePhaseOneEval_mem_FP

/-- The complete encoded evaluator has a quadratic output-length bound. -/
theorem affinePhaseOneEval_length_le (z : List Bool) :
    (affinePhaseOneEval z).length ≤ 2 ^ 65 * (z.length + 1) ^ 2 :=
  Internal.affinePhaseOneEval_length_le z

end Algebraic.Cutwidth.Extractor
