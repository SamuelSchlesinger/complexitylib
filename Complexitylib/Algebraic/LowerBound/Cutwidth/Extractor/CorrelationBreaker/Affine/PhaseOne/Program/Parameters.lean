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
public import Complexitylib.Tactic.PolyTime.Init
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.PhaseOne.Program.Parameters.Internal

/-!
# One uniform evaluator for the selected first affine phase

The evaluator derives the component parameters from the original source
and advice lengths and the unary tampering and target inputs. It normalizes
the right word to the chosen width and runs the actual first extraction,
advice construction, and growing-depth final extraction. Canonical words
agree exactly with the semantic first phase at the same selected parameters.

All component guards are discharged by the finite chooser. The polynomial-
time theorem holds on every encoded input, including malformed pairings and
infeasible source-entropy requests. The statistical source-capacity premise
belongs to the separate extraction theorem, not the evaluator.
-/

public section

namespace Algebraic.Cutwidth.Extractor

/-- Every selected runtime output has the chosen growing-depth width. -/
theorem affinePhaseOneSelectedRuntime_length (t target : Nat) (x y advice : List Bool) :
    (affinePhaseOneSelectedRuntime t target x y advice).length =
      2 ^ growingMatchedBlockDepth t *
        affinePhaseOneScale x.length t advice.length target :=
  Internal.affinePhaseOneSelectedRuntime_length t target x y advice

/-- The output width is at most a linear leaf-count bound times the computed scale. -/
theorem affinePhaseOneSelectedRuntime_length_le (t target : Nat) (x y advice : List Bool) :
    (affinePhaseOneSelectedRuntime t target x y advice).length ≤
      2 ^ 65 * (t + 1) * affinePhaseOneScale x.length t advice.length target :=
  Internal.affinePhaseOneSelectedRuntime_length_le t target x y advice

/-- Canonical words compute the actual semantic phase at the selected parameters. -/
theorem affinePhaseOneSelectedRuntime_eq (n t target : Nat) (advice : List Bool)
    (x : Fin n → Bool) (y : Fin (affinePhaseOneRightBits n t advice.length target) → Bool) :
    affinePhaseOneSelectedRuntime t target (List.ofFn x) (List.ofFn y) advice =
      List.ofFn (affinePhaseOneOutput n (affinePhaseOneRightBits n t advice.length target)
        (growingMatchedBlockDepth t) (affinePhaseOneInitialScale n t advice.length target)
        (affinePhaseOneLocalError target) (affinePhaseOneScale n t advice.length target)
        (adviceErrorExponent advice.length (affinePhaseOneLocalError target))
        (affinePhaseOneLocalError target) x y advice) :=
  Internal.affinePhaseOneSelectedRuntime_eq n t target advice x y

open Complexity in
/-- One uniform program computes all chooser values and runs all three components. -/
@[polytime] theorem affinePhaseOneSelectedRuntime_mem_FP {t target : List Bool → Nat}
    {x y advice : List Bool → List Bool} (ht : UnaryFn t) (htarget : UnaryFn target)
    (hx : x ∈ FP) (hy : y ∈ FP) (hadvice : advice ∈ FP) :
    (fun z => affinePhaseOneSelectedRuntime (t z) (target z) (x z) (y z) (advice z)) ∈ FP :=
  Internal.affinePhaseOneSelectedRuntime_mem_FP ht htarget hx hy hadvice

open Complexity in
/-- The compact paired input keeps both original words and advice, with two unary parameters. -/
theorem affinePhaseOneSelectedEval_pair (x y advice parameter targetWord : List Bool) :
    affinePhaseOneSelectedEval
      (pair (pair x (pair y advice)) (pair parameter targetWord)) =
      affinePhaseOneSelectedRuntime parameter.length targetWord.length x y advice :=
  Internal.affinePhaseOneSelectedEval_pair x y advice parameter targetWord

open Complexity in
/-- The single paired evaluator serializes the actual selected semantic map exactly. -/
theorem affinePhaseOneSelectedEval_eq (n t target : Nat) (advice : List Bool)
    (x : Fin n → Bool) (y : Fin (affinePhaseOneRightBits n t advice.length target) → Bool) :
    affinePhaseOneSelectedEval (pair (pair (List.ofFn x) (pair (List.ofFn y) advice))
      (pair (List.replicate t true) (List.replicate target true))) =
      List.ofFn (affinePhaseOneOutput n (affinePhaseOneRightBits n t advice.length target)
        (growingMatchedBlockDepth t) (affinePhaseOneInitialScale n t advice.length target)
        (affinePhaseOneLocalError target) (affinePhaseOneScale n t advice.length target)
        (adviceErrorExponent advice.length (affinePhaseOneLocalError target))
        (affinePhaseOneLocalError target) x y advice) :=
  Internal.affinePhaseOneSelectedEval_eq n t target advice x y

open Complexity in
/-- A total FP certificate includes unary parameter computation and the actual payload loop. -/
@[polytime] theorem affinePhaseOneSelectedEval_mem_FP : affinePhaseOneSelectedEval ∈ FP :=
  Internal.affinePhaseOneSelectedEval_mem_FP

end Algebraic.Cutwidth.Extractor
