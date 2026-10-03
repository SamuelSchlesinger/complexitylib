/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.PhaseOne.Program.Parameters.Defs
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.PhaseOne.Defs
public import Complexitylib.Classes.P.Defs
public import Complexitylib.Classes.P.Unary.Defs
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.PhaseOne.Program
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.PhaseOne.Parameters
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.PhaseOne.Parameters.Unary
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Advice.Extraction.Program
import Complexitylib.Tactic.PolyTime

/-!
# Correctness of the selected first-phase string evaluator

The finite chooser discharges all component guards, while canonical right
words are unchanged by normalization. The runtime certificate composes the
public unary parameter rules with the actual three-stage program; it places
no source-capacity or statistical restriction on an encoded input.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

open Complexity

theorem affinePhaseOneSelectedRuntime_length (t target : Nat) (x y advice : List Bool) :
    (affinePhaseOneSelectedRuntime t target x y advice).length =
      2 ^ growingMatchedBlockDepth t *
        affinePhaseOneScale x.length t advice.length target := by
  dsimp only [affinePhaseOneSelectedRuntime]
  rw [affinePhaseOneRuntime_length,
    ite_eq_left (affinePhaseOneParameters_growing_guard x.length t advice.length target)]

theorem affinePhaseOneSelectedRuntime_length_le (t target : Nat) (x y advice : List Bool) :
    (affinePhaseOneSelectedRuntime t target x y advice).length ≤
      2 ^ 65 * (t + 1) * affinePhaseOneScale x.length t advice.length target :=
  affinePhaseOneRuntime_length_le _ _ _ _ _ _ _ _ _

theorem affinePhaseOneSelectedRuntime_eq (n t target : Nat) (advice : List Bool)
    (x : Fin n → Bool) (y : Fin (affinePhaseOneRightBits n t advice.length target) → Bool) :
    affinePhaseOneSelectedRuntime t target (List.ofFn x) (List.ofFn y) advice =
      List.ofFn (affinePhaseOneOutput n (affinePhaseOneRightBits n t advice.length target)
        (growingMatchedBlockDepth t) (affinePhaseOneInitialScale n t advice.length target)
        (affinePhaseOneLocalError target) (affinePhaseOneScale n t advice.length target)
        (adviceErrorExponent advice.length (affinePhaseOneLocalError target))
        (affinePhaseOneLocalError target) x y advice) := by
  simp only [affinePhaseOneSelectedRuntime, List.length_ofFn]
  rw [adviceSelectedRightWord_eq _ _ List.length_ofFn]
  apply affinePhaseOneRuntime_eq_affinePhaseOneOutput
  · exact ⟨affinePhaseOneParameters_initial_room n t advice.length target, le_rfl,
      affinePhaseOneParameters_initial_error n t advice.length target,
      affinePhaseOneParameters_initial_length n t advice.length target⟩
  · exact affinePhaseOneParameters_advice_guard n t advice.length target
  · exact affinePhaseOneParameters_growing_guard n t advice.length target

theorem affinePhaseOneSelectedRuntime_mem_FP {t target : List Bool → Nat}
    {x y advice : List Bool → List Bool} (ht : UnaryFn t) (htarget : UnaryFn target)
    (hx : x ∈ FP) (hy : y ∈ FP) (hadvice : advice ∈ FP) :
    (fun z => affinePhaseOneSelectedRuntime (t z) (target z) (x z) (y z) (advice z)) ∈ FP := by
  polytime [affinePhaseOneSelectedRuntime]

theorem affinePhaseOneSelectedEval_pair (x y advice parameter targetWord : List Bool) :
    affinePhaseOneSelectedEval
      (pair (pair x (pair y advice)) (pair parameter targetWord)) =
      affinePhaseOneSelectedRuntime parameter.length targetWord.length x y advice := by
  simp only [affinePhaseOneSelectedEval, pairFst_pair, pairSnd_pair]

theorem affinePhaseOneSelectedEval_eq (n t target : Nat) (advice : List Bool)
    (x : Fin n → Bool) (y : Fin (affinePhaseOneRightBits n t advice.length target) → Bool) :
    affinePhaseOneSelectedEval (pair (pair (List.ofFn x) (pair (List.ofFn y) advice))
      (pair (List.replicate t true) (List.replicate target true))) =
      List.ofFn (affinePhaseOneOutput n (affinePhaseOneRightBits n t advice.length target)
        (growingMatchedBlockDepth t) (affinePhaseOneInitialScale n t advice.length target)
        (affinePhaseOneLocalError target) (affinePhaseOneScale n t advice.length target)
        (adviceErrorExponent advice.length (affinePhaseOneLocalError target))
        (affinePhaseOneLocalError target) x y advice) := by
  rw [affinePhaseOneSelectedEval_pair, List.length_replicate, List.length_replicate]
  exact affinePhaseOneSelectedRuntime_eq n t target advice x y

theorem affinePhaseOneSelectedEval_mem_FP : affinePhaseOneSelectedEval ∈ FP := by
  unfold affinePhaseOneSelectedEval
  apply affinePhaseOneSelectedRuntime_mem_FP <;> polytime

end Algebraic.Cutwidth.Extractor.Internal
