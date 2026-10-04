/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.Iteration.Program.Defs
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.Iteration.Defs
public import Complexitylib.Classes.P.Defs
public import Complexitylib.Classes.P.Unary.Defs
public import Complexitylib.Tactic.PolyTime.Init
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.Iteration.Program.Internal

/-!
# Uniform execution of repeated actual affine rounds

The semantic correspondence reads the same original source words at every
round. The polynomial-time certificate bounds the complete encoded state,
including the original words, unary parameters, and arbitrary initial row.
It is unconditional on malformed inputs and invalid numerical parameters.
-/

public section

namespace Algebraic.Cutwidth.Extractor

open Complexity

/-- One further iteration performs the actual round on the current row. -/
theorem affineRoundsRuntime_succ (t L e i : Nat) (x y row : List Bool) :
    affineRoundsRuntime t L e (i + 1) x y row =
      affineRoundRuntime t L e x y (affineRoundsRuntime t L e i x y row) :=
  Internal.affineRoundsRuntime_succ t L e i x y row

/-- An encoded step preserves the original context exactly. -/
theorem affineRoundsStepEval_pair (t L e : Nat) (x y row : List Bool) :
    affineRoundsStepEval (pair (affineRoundsContextWord t L e x y) row) =
      pair (affineRoundsContextWord t L e x y) (affineRoundRuntime t L e x y row) :=
  Internal.affineRoundsStepEval_pair t L e x y row

/-- Every encoded iterate contains the original context and the actual evolving row. -/
theorem affineRoundsStepEval_iterate (t L e i : Nat) (x y row : List Bool) :
    affineRoundsStepEval^[i] (pair (affineRoundsContextWord t L e x y) row) =
      pair (affineRoundsContextWord t L e x y) (affineRoundsRuntime t L e i x y row) :=
  Internal.affineRoundsStepEval_iterate t L e i x y row

/-- Every iterate is bounded by the initial row and one round output bound. -/
theorem affineRoundsRuntime_length_le (t L e i : Nat) (x y row : List Bool) :
    (affineRoundsRuntime t L e i x y row).length ≤ row.length + 2 ^ 65 * (t + 1) * L :=
  Internal.affineRoundsRuntime_length_le t L e i x y row

/-- The complete encoded state includes both original sources and all unary parameters. -/
theorem affineRoundsState_length_le (t L e i : Nat) (x y row : List Bool) :
    (pair (affineRoundsContextWord t L e x y)
      (affineRoundsRuntime t L e i x y row)).length ≤
        2 * (affineRoundsContextWord t L e x y).length + 2 +
          row.length + 2 ^ 65 * (t + 1) * L :=
  Internal.affineRoundsState_length_le t L e i x y row

/-- Canonical words follow exactly the semantic iteration on the same original sources. -/
theorem affineRoundsRuntime_eq_affineRoundsOutput (n d t L e i : Nat)
    (right : MatchedBlockRuntimeValid d 24 L e)
    (rowGuard : MatchedBlockRuntimeValid
      (matchedBlockOutputBits (growingMatchedBlockDepth t) L) 24 L e)
    (last : GrowingMatchedBlockRuntimeValid n t L e)
    (x : Fin n → Bool) (y : Fin d → Bool)
    (row : Fin (matchedBlockOutputBits (growingMatchedBlockDepth t) L) → Bool) :
    affineRoundsRuntime t L e i (List.ofFn x) (List.ofFn y) (List.ofFn row) =
      List.ofFn (affineRoundsOutput n d (growingMatchedBlockDepth t) L e i x y row) :=
  Internal.affineRoundsRuntime_eq_affineRoundsOutput n d t L e i right rowGuard last x y row

/-- Encoding the immutable source context and unary parameters is polynomial-time. -/
@[polytime] theorem affineRoundsContextWord_mem_FP {t L e : List Bool → Nat}
    {x y : List Bool → List Bool} (ht : UnaryFn t) (hL : UnaryFn L) (he : UnaryFn e)
    (hx : x ∈ FP) (hy : y ∈ FP) :
    (fun z => affineRoundsContextWord (t z) (L z) (e z) (x z) (y z)) ∈ FP :=
  Internal.affineRoundsContextWord_mem_FP ht hL he hx hy

/-- One total encoded step is polynomial-time on every word. -/
@[polytime] theorem affineRoundsStepEval_mem_FP : affineRoundsStepEval ∈ FP :=
  Internal.affineRoundsStepEval_mem_FP

/-- A unary number of actual rounds is uniformly polynomial-time with no validity promise. -/
@[polytime] theorem affineRoundsRuntime_mem_FP {t L e i : List Bool → Nat}
    {x y row : List Bool → List Bool} (ht : UnaryFn t) (hL : UnaryFn L) (he : UnaryFn e)
    (hi : UnaryFn i) (hx : x ∈ FP) (hy : y ∈ FP) (hrow : row ∈ FP) :
    (fun z => affineRoundsRuntime (t z) (L z) (e z) (i z) (x z) (y z) (row z)) ∈ FP :=
  Internal.affineRoundsRuntime_mem_FP ht hL he hi hx hy hrow

/-- The single evaluator decodes the original sources, row, parameters, and round count. -/
theorem affineRoundsEval_pair (t L e : Nat) (x y row rounds : List Bool) :
    affineRoundsEval (pair (pair (affineRoundsContextWord t L e x y) row) rounds) =
      affineRoundsRuntime t L e rounds.length x y row :=
  Internal.affineRoundsEval_pair t L e x y row rounds

/-- One total polynomial-time evaluator runs the complete repeated-round program. -/
@[polytime] theorem affineRoundsEval_mem_FP : affineRoundsEval ∈ FP :=
  Internal.affineRoundsEval_mem_FP

/-- The full evaluator has a quadratic output bound, including the zero-round input row. -/
theorem affineRoundsEval_length_le (z : List Bool) :
    (affineRoundsEval z).length ≤ z.length + 2 ^ 65 * (z.length + 1) ^ 2 :=
  Internal.affineRoundsEval_length_le z

end Algebraic.Cutwidth.Extractor
