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
public import Complexitylib.Classes.P.Unary.Defs
public import Complexitylib.Classes.P.Defs
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.Round.Program
import Complexitylib.Classes.P.Iterate
import Complexitylib.Tactic.PolyTime

/-!
# Repeated-round semantics and the complete encoded-state bound

The exact state correspondence keeps both original sources and every unary
parameter. Bounding this full encoding, including the arbitrary initial
row, supplies the bounded-iteration theorem. Polynomial time has no runtime
validity or statistical hypotheses.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

open Complexity

theorem affineRoundsRuntime_succ (t L e i : Nat) (x y row : List Bool) :
    affineRoundsRuntime t L e (i + 1) x y row =
      affineRoundRuntime t L e x y (affineRoundsRuntime t L e i x y row) :=
  Function.iterate_succ_apply' _ _ _

theorem affineRoundsStepEval_pair (t L e : Nat) (x y row : List Bool) :
    affineRoundsStepEval (pair (affineRoundsContextWord t L e x y) row) =
      pair (affineRoundsContextWord t L e x y) (affineRoundRuntime t L e x y row) := by
  simp only [affineRoundsStepEval, affineRoundsContextWord, pairFst_pair,
    pairSnd_pair, List.length_replicate]

theorem affineRoundsStepEval_iterate (t L e i : Nat) (x y row : List Bool) :
    affineRoundsStepEval^[i] (pair (affineRoundsContextWord t L e x y) row) =
      pair (affineRoundsContextWord t L e x y) (affineRoundsRuntime t L e i x y row) := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [Function.iterate_succ_apply', ih, affineRoundsStepEval_pair, affineRoundsRuntime_succ]

theorem affineRoundsRuntime_length_le (t L e i : Nat) (x y row : List Bool) :
    (affineRoundsRuntime t L e i x y row).length ≤ row.length + 2 ^ 65 * (t + 1) * L := by
  cases i with
  | zero => exact Nat.le_add_right _ _
  | succ i =>
    rw [affineRoundsRuntime_succ]
    exact (affineRoundRuntime_length_le _ _ _ _ _ _).trans (Nat.le_add_left _ _)

theorem affineRoundsState_length_le (t L e i : Nat) (x y row : List Bool) :
    (pair (affineRoundsContextWord t L e x y)
      (affineRoundsRuntime t L e i x y row)).length ≤
        2 * (affineRoundsContextWord t L e x y).length + 2 +
          row.length + 2 ^ 65 * (t + 1) * L := by
  rw [pair_length]
  have := affineRoundsRuntime_length_le t L e i x y row
  lia

theorem affineRoundsRuntime_eq_affineRoundsOutput (n d t L e i : Nat)
    (right : MatchedBlockRuntimeValid d 24 L e)
    (rowGuard : MatchedBlockRuntimeValid
      (matchedBlockOutputBits (growingMatchedBlockDepth t) L) 24 L e)
    (last : GrowingMatchedBlockRuntimeValid n t L e)
    (x : Fin n → Bool) (y : Fin d → Bool)
    (row : Fin (matchedBlockOutputBits (growingMatchedBlockDepth t) L) → Bool) :
    affineRoundsRuntime t L e i (List.ofFn x) (List.ofFn y) (List.ofFn row) =
      List.ofFn (affineRoundsOutput n d (growingMatchedBlockDepth t) L e i x y row) := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [affineRoundsRuntime_succ, ih]
    exact affineRoundRuntime_eq_affineRoundOutput n d t L e right rowGuard last x y _

theorem affineRoundsContextWord_mem_FP {t L e : List Bool → Nat}
    {x y : List Bool → List Bool} (ht : UnaryFn t) (hL : UnaryFn L) (he : UnaryFn e)
    (hx : x ∈ FP) (hy : y ∈ FP) :
    (fun z => affineRoundsContextWord (t z) (L z) (e z) (x z) (y z)) ∈ FP := by
  polytime [affineRoundsContextWord]

theorem affineRoundsStepEval_mem_FP : affineRoundsStepEval ∈ FP := by
  polytime [affineRoundsStepEval]

theorem affineRoundsRuntime_mem_FP {t L e i : List Bool → Nat}
    {x y row : List Bool → List Bool} (ht : UnaryFn t) (hL : UnaryFn L) (he : UnaryFn e)
    (hi : UnaryFn i) (hx : x ∈ FP) (hy : y ∈ FP) (hrow : row ∈ FP) :
    (fun z => affineRoundsRuntime (t z) (L z) (e z) (i z) (x z) (y z) (row z)) ∈ FP := by
  have context := affineRoundsContextWord_mem_FP ht hL he hx hy
  have start : (fun z =>
      pair (affineRoundsContextWord (t z) (L z) (e z) (x z) (y z)) (row z)) ∈ FP := by
    polytime
  have width : UnaryFn fun z =>
      2 * (affineRoundsContextWord (t z) (L z) (e z) (x z) (y z)).length + 2 +
        (row z).length + 2 ^ 65 * (t z + 1) * L z := by
    polytime
  have loop := iterate_mem_FP affineRoundsStepEval_mem_FP start hi.mem_FP width.mem_FP
    (fun z j _ => by
      rw [affineRoundsStepEval_iterate, List.length_replicate]
      exact affineRoundsState_length_le _ _ _ _ _ _ _)
  have projected : (fun z => pairSnd
      (affineRoundsStepEval^[(List.replicate (i z) false).length]
        (pair (affineRoundsContextWord (t z) (L z) (e z) (x z) (y z)) (row z)))) ∈ FP := by
    polytime
  exact mem_FP_of_eq projected fun z => by
    simp only [List.length_replicate, affineRoundsStepEval_iterate, pairSnd_pair]

theorem affineRoundsEval_pair (t L e : Nat) (x y row rounds : List Bool) :
    affineRoundsEval (pair (pair (affineRoundsContextWord t L e x y) row) rounds) =
      affineRoundsRuntime t L e rounds.length x y row := by
  simp only [affineRoundsEval, affineRoundsContextWord, pairFst_pair,
    pairSnd_pair, List.length_replicate]

theorem affineRoundsEval_mem_FP : affineRoundsEval ∈ FP := by
  unfold affineRoundsEval
  apply affineRoundsRuntime_mem_FP <;> polytime

theorem affineRoundsEval_length_le (z : List Bool) :
    (affineRoundsEval z).length ≤ z.length + 2 ^ 65 * (z.length + 1) ^ 2 := by
  have fst := pairFst_length_le
  have snd := pairSnd_length_le
  have bound := affineRoundsRuntime_length_le
    (pairFst (pairSnd (pairSnd (pairFst (pairFst z))))).length
    (pairFst (pairSnd (pairSnd (pairSnd (pairFst (pairFst z)))))).length
    (pairSnd (pairSnd (pairSnd (pairSnd (pairFst (pairFst z)))))).length
    (pairSnd z).length (pairFst (pairFst (pairFst z)))
    (pairFst (pairSnd (pairFst (pairFst z)))) (pairSnd (pairFst z))
  have parameter := (fst (pairSnd (pairSnd (pairFst (pairFst z))))).trans
    ((snd (pairSnd (pairFst (pairFst z)))).trans
      ((snd (pairFst (pairFst z))).trans ((fst (pairFst z)).trans (fst z))))
  have scale := (fst (pairSnd (pairSnd (pairSnd (pairFst (pairFst z)))))).trans
    ((snd (pairSnd (pairSnd (pairFst (pairFst z))))).trans
      ((snd (pairSnd (pairFst (pairFst z)))).trans
        ((snd (pairFst (pairFst z))).trans ((fst (pairFst z)).trans (fst z)))))
  have row := (snd (pairFst z)).trans (fst z)
  exact bound.trans (Nat.add_le_add row (by nlinarith))

end Algebraic.Cutwidth.Extractor.Internal
