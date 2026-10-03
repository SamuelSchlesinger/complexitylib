/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Advice.Program.Defs
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Advice
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.FlipFlop.Program

/-!
# Advice-loop invariants and exact encoded transitions

The invariant bounds the whole encoded state. The two original words and
parameters are constant, the advice only shrinks, and the current state is
bounded by its original length or the fixed refresh width.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

open Complexity

theorem adviceInitialWord_length (L : Nat) (y : List Bool) :
    (adviceInitialWord L y).length = matchedBlockOutputBits 64 L := by
  simp only [adviceInitialWord, List.length_take, List.length_append, List.length_replicate]
  exact min_eq_left (by lia)

theorem adviceInitialState_ofFn (m L : Nat) (y : Fin m → Bool) :
    List.ofFn (adviceInitialState m L y) = adviceInitialWord L (List.ofFn y) := by
  apply List.ext_getElem
  · rw [List.length_ofFn, adviceInitialWord_length]
  · intro i hi hj
    simp only [List.getElem_ofFn, adviceInitialState, adviceInitialWord, List.getElem_take]
    by_cases inside : i < (List.ofFn y).length
    · rw [List.getElem?_eq_getElem inside, Option.getD_some, List.getElem_append_left inside]
    · rw [List.getElem?_eq_none (by lia), Option.getD_none,
        List.getElem_append_right (by lia), List.getElem_replicate]

theorem decodeAdviceRunState_encode (state : AdviceRunState) :
    decodeAdviceRunState (encodeAdviceRunState state) = state := by
  cases state
  simp only [decodeAdviceRunState, encodeAdviceRunState, pairFst_pair, pairSnd_pair,
    List.length_replicate]

theorem adviceRunStepEval_encode (state : AdviceRunState) :
    adviceRunStepEval (encodeAdviceRunState state) =
      encodeAdviceRunState (adviceRunStep state) := by
  rw [adviceRunStepEval, decodeAdviceRunState_encode]

theorem adviceRunStepEval_iterate (state : AdviceRunState) (i : Nat) :
    adviceRunStepEval^[i] (encodeAdviceRunState state) =
      encodeAdviceRunState (adviceRunStep^[i] state) := by
  have commute : Function.Semiconj encodeAdviceRunState adviceRunStep adviceRunStepEval :=
    fun state => (adviceRunStepEval_encode state).symm
  exact (commute.iterate_right i state).symm

theorem encodeAdviceRunState_length (state : AdviceRunState) :
    (encodeAdviceRunState state).length =
      4 * state.x.length + 2 * state.y.length + 2 * state.scale + 2 * state.error +
        2 * state.remaining.length + state.q.length + 12 := by
  simp only [encodeAdviceRunState, pair_length, List.length_replicate]
  lia

theorem adviceRunStep_iterate_invariants (state : AdviceRunState) (i : Nat) :
    (adviceRunStep^[i] state).x = state.x ∧
      (adviceRunStep^[i] state).y = state.y ∧
      (adviceRunStep^[i] state).scale = state.scale ∧
      (adviceRunStep^[i] state).error = state.error ∧
      (adviceRunStep^[i] state).remaining.length ≤ state.remaining.length ∧
      (adviceRunStep^[i] state).q.length ≤
        max state.q.length (matchedBlockOutputBits 64 state.scale) := by
  induction i with
  | zero => exact ⟨rfl, rfl, rfl, rfl, le_rfl, le_max_left _ _⟩
  | succ i ih =>
    rcases ih with ⟨hx, hy, hL, he, ha, hq⟩
    rw [Function.iterate_succ_apply']
    refine ⟨hx, hy, hL, he, ?_, ?_⟩
    · change ((adviceRunStep^[i] state).remaining.drop 1).length ≤ _
      rw [List.length_drop]
      lia
    · simp only [adviceRunStep]
      split
      · exact hq
      · exact (flipFlopStepRuntime_length_le _ _ _ _ _ _).trans
          (hL ▸ le_max_right state.q.length (matchedBlockOutputBits 64 state.scale))

theorem adviceRun_length_le (L e : Nat) (x y advice : List Bool) (i : Nat) :
    (encodeAdviceRunState (adviceRun L e x y advice i)).length ≤
      4 * x.length + 2 * y.length + 2 * L + 2 * e + 2 * advice.length +
        matchedBlockOutputBits 64 L + 12 := by
  rcases adviceRunStep_iterate_invariants (adviceRunInitial L e x y advice) i with
    ⟨hx, hy, hL, he, ha, hq⟩
  simp only [adviceRunInitial, adviceInitialWord_length, max_self] at hx hy hL he ha hq
  rw [encodeAdviceRunState_length]
  unfold adviceRun adviceRunInitial
  rw [hx, hy, hL, he]
  lia

theorem adviceRunStep_iterate_fold (L e : Nat) (x y advice q : List Bool) :
    adviceRunStep^[advice.length] ⟨x, y, L, e, advice, q⟩ =
      ⟨x, y, L, e, [], advice.foldl (flipFlopStepRuntime L e x y) q⟩ := by
  induction advice generalizing q with
  | nil => rfl
  | cons bit rest ih =>
    simp only [List.length_cons, Function.iterate_succ_apply, adviceRunStep,
      List.drop_succ_cons, List.drop_zero, Nat.add_eq_zero_iff, Nat.one_ne_zero,
      and_false, ite_false, List.getElem?_cons_zero, Option.getD_some, List.foldl_cons]
    exact ih _

theorem adviceRun_fold (L e : Nat) (x y advice : List Bool) :
    adviceRun L e x y advice advice.length =
      ⟨x, y, L, e, [], advice.foldl (flipFlopStepRuntime L e x y) (adviceInitialWord L y)⟩ :=
  adviceRunStep_iterate_fold L e x y advice _

end Algebraic.Cutwidth.Extractor.Internal
