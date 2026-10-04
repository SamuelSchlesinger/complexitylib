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
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.Iteration.Program
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.PhaseOne.Program
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.PhaseOne.Parameters
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.PhaseOne.Parameters.Unary
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.Round.Parameters
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.Round.Program
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Advice.Extraction.Program
import Complexitylib.Tactic.PolyTime

/-!
# Correctness and polynomial time of the complete affine program

The explicit runtime composes the checked first phase and bounded round
iteration. The selected runtime discharges every component guard using the
same boosted chooser as the statistical construction. The whole program
has one unconditional FP certificate, including parameter computation and
malformed encoded inputs.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

open Complexity

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
        L₀ e₀ L₁ e₁ er rounds x y advice) := by
  unfold affineCorrelationBreakerRuntime affineCorrelationBreaker
  rw [affinePhaseOneRuntime_eq_affinePhaseOneOutput n d t L₀ e₀ L₁ e₁ er
    first adviceGuard last x y advice]
  exact affineRoundsRuntime_eq_affineRoundsOutput n d t L₁ er rounds right rowGuard last x y _

theorem affineCorrelationBreakerRuntime_length (t L₀ e₀ L₁ e₁ er rounds : Nat)
    (x y advice : List Bool) :
    (affineCorrelationBreakerRuntime t L₀ e₀ L₁ e₁ er rounds x y advice).length =
      if GrowingMatchedBlockRuntimeValid x.length t L₁ er then
        2 ^ growingMatchedBlockDepth t * L₁ else 0 := by
  cases rounds with
  | zero => exact affinePhaseOneRuntime_length t L₀ e₀ L₁ e₁ er x y advice
  | succ i =>
    unfold affineCorrelationBreakerRuntime
    rw [affineRoundsRuntime_succ, affineRoundRuntime_length]

theorem affineCorrelationBreakerRuntime_length_le (t L₀ e₀ L₁ e₁ er rounds : Nat)
    (x y advice : List Bool) :
    (affineCorrelationBreakerRuntime t L₀ e₀ L₁ e₁ er rounds x y advice).length ≤
      2 ^ 65 * (t + 1) * L₁ := by
  cases rounds with
  | zero => exact affinePhaseOneRuntime_length_le t L₀ e₀ L₁ e₁ er x y advice
  | succ i =>
    unfold affineCorrelationBreakerRuntime
    rw [affineRoundsRuntime_succ]
    exact affineRoundRuntime_length_le _ _ _ _ _ _

theorem affineCorrelationBreakerRuntime_mem_FP {t L₀ e₀ L₁ e₁ er rounds : List Bool → Nat}
    {x y advice : List Bool → List Bool}
    (ht : UnaryFn t) (hL₀ : UnaryFn L₀) (he₀ : UnaryFn e₀)
    (hL₁ : UnaryFn L₁) (he₁ : UnaryFn e₁) (her : UnaryFn er) (hrounds : UnaryFn rounds)
    (hx : x ∈ FP) (hy : y ∈ FP) (hadvice : advice ∈ FP) :
    (fun z => affineCorrelationBreakerRuntime (t z) (L₀ z) (e₀ z) (L₁ z) (e₁ z) (er z)
      (rounds z) (x z) (y z) (advice z)) ∈ FP := by
  polytime [affineCorrelationBreakerRuntime]

theorem affineCorrelationBreakerSelectedRuntime_length (t target : Nat) (x y advice : List Bool) :
    (affineCorrelationBreakerSelectedRuntime t target x y advice).length =
      2 ^ growingMatchedBlockDepth t *
        affinePhaseOneScale x.length t advice.length (affineIterationTarget t target) := by
  dsimp only [affineCorrelationBreakerSelectedRuntime]
  rw [affineCorrelationBreakerRuntime_length, ite_eq_left
    (affinePhaseOneParameters_growing_guard x.length t advice.length
      (affineIterationTarget t target))]

theorem affineCorrelationBreakerSelectedRuntime_length_le (t target : Nat)
    (x y advice : List Bool) :
    (affineCorrelationBreakerSelectedRuntime t target x y advice).length ≤
      2 ^ 65 * (t + 1) *
        affinePhaseOneScale x.length t advice.length (affineIterationTarget t target) :=
  affineCorrelationBreakerRuntime_length_le _ _ _ _ _ _ _ _ _ _

theorem affineCorrelationBreakerSelectedRuntime_eq (n t target : Nat) (advice : List Bool)
    (x : Fin n → Bool)
    (y : Fin (affinePhaseOneRightBits n t advice.length (affineIterationTarget t target)) → Bool) :
    affineCorrelationBreakerSelectedRuntime t target (List.ofFn x) (List.ofFn y) advice =
      List.ofFn (affineCorrelationBreakerSelected n t target advice x y) := by
  simp only [affineCorrelationBreakerSelectedRuntime, List.length_ofFn]
  rw [adviceSelectedRightWord_eq _ _ List.length_ofFn]
  apply affineCorrelationBreakerRuntime_eq
  · exact ⟨affinePhaseOneParameters_initial_room n t advice.length _, le_rfl,
      affinePhaseOneParameters_initial_error n t advice.length _,
      affinePhaseOneParameters_initial_length n t advice.length _⟩
  · exact affinePhaseOneParameters_advice_guard n t advice.length _
  · exact affineRoundParameters_right_guard n t advice.length _
  · exact affineRoundParameters_row_guard n t advice.length _
  · exact affinePhaseOneParameters_growing_guard n t advice.length _

theorem affineCorrelationBreakerSelectedRuntime_mem_FP {t target : List Bool → Nat}
    {x y advice : List Bool → List Bool} (ht : UnaryFn t) (htarget : UnaryFn target)
    (hx : x ∈ FP) (hy : y ∈ FP) (hadvice : advice ∈ FP) :
    (fun z => affineCorrelationBreakerSelectedRuntime (t z) (target z)
      (x z) (y z) (advice z)) ∈ FP := by
  have rounds : UnaryFn fun z => affineIterationRounds (t z) := by
    polytime [affineIterationRounds]
  have boosted : UnaryFn fun z => affineIterationTarget (t z) (target z) := by
    polytime [affineIterationTarget]
  unfold affineCorrelationBreakerSelectedRuntime
  apply affineCorrelationBreakerRuntime_mem_FP <;> polytime

theorem affineCorrelationBreakerSelectedEval_pair (x y advice parameter targetWord : List Bool) :
    affineCorrelationBreakerSelectedEval
      (pair (pair x (pair y advice)) (pair parameter targetWord)) =
      affineCorrelationBreakerSelectedRuntime parameter.length targetWord.length x y advice := by
  simp only [affineCorrelationBreakerSelectedEval, pairFst_pair, pairSnd_pair]

theorem affineCorrelationBreakerSelectedEval_eq (n t target : Nat) (advice : List Bool)
    (x : Fin n → Bool)
    (y : Fin (affinePhaseOneRightBits n t advice.length (affineIterationTarget t target)) → Bool) :
    affineCorrelationBreakerSelectedEval (pair (pair (List.ofFn x) (pair (List.ofFn y) advice))
      (pair (List.replicate t true) (List.replicate target true))) =
      List.ofFn (affineCorrelationBreakerSelected n t target advice x y) := by
  rw [affineCorrelationBreakerSelectedEval_pair, List.length_replicate, List.length_replicate]
  exact affineCorrelationBreakerSelectedRuntime_eq n t target advice x y

theorem affineCorrelationBreakerSelectedEval_mem_FP : affineCorrelationBreakerSelectedEval ∈ FP := by
  unfold affineCorrelationBreakerSelectedEval
  apply affineCorrelationBreakerSelectedRuntime_mem_FP <;> polytime

end Algebraic.Cutwidth.Extractor.Internal
