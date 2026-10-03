/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.FlipFlop.Program.Defs
public import Complexitylib.Classes.P.Unary.Defs
public import Complexitylib.Classes.P.Defs
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Scheduled.Matched.Program
import Mathlib.Data.Fin.Tuple.Take
import Complexitylib.Tactic.PolyTime

/-!
# Correctness and closure proofs for the concrete advice-bit program

Canonical words follow the same three-call and eight-call computations as
the vector definitions. Polynomial time is composed from the registered
matched-extractor certificate, including both conditional choices. The final
refresh gives a uniform output-size bound even on invalid parameters.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

open Complexity

theorem flipFlopSeedPrefix_ofFn (L : Nat) (q : Fin (matchedBlockOutputBits 64 L) → Bool) :
    List.ofFn (flipFlopSeedPrefix L q) = (List.ofFn q).take (matchedBlockSeedBits L) :=
  Fin.ofFn_take_eq_take_ofFn
    (Nat.mul_le_mul_right L (show 2 ^ 24 ≤ 2 ^ 64 by decide)) q

theorem flipFlopLookAheadRuntime_eq (n L e : Nat)
    (left : MatchedBlockRuntimeValid n 24 L e)
    (state : MatchedBlockRuntimeValid (matchedBlockOutputBits 64 L) 24 L e)
    (x : Fin n → Bool) (q : Fin (matchedBlockOutputBits 64 L) → Bool) :
    flipFlopLookAheadRuntime L e (List.ofFn x) (List.ofFn q) =
      pair (List.ofFn (flipFlopLookAhead n L e x q).1)
        (List.ofFn (flipFlopLookAhead n L e x q).2) := by
  let r₁ := matchedBlockExtractor n 24 L e x (flipFlopSeedPrefix L q)
  let s₂ := matchedBlockExtractor (matchedBlockOutputBits 64 L) 24 L e q r₁
  have first : matchedBlockExtractorRuntime 24 L e (List.ofFn x)
      ((List.ofFn q).take (matchedBlockSeedBits L)) = List.ofFn r₁ := by
    rw [← flipFlopSeedPrefix_ofFn L q]
    exact matchedBlockExtractorRuntime_eq_matchedBlockExtractor n 24 L e left x _
  have second := (congrArg (matchedBlockExtractorRuntime 24 L e (List.ofFn q)) first).trans
    (matchedBlockExtractorRuntime_eq_matchedBlockExtractor _ 24 L e state q r₁)
  have third := (congrArg (matchedBlockExtractorRuntime 24 L e (List.ofFn x)) second).trans
    (matchedBlockExtractorRuntime_eq_matchedBlockExtractor n 24 L e left x s₂)
  simpa only [flipFlopLookAheadRuntime, flipFlopLookAhead, matchedBlockOutputBits,
    matchedBlockSeedBits, r₁, s₂] using congrArg₂ pair first third

theorem flipFlopStepRuntime_eq (n m L e : Nat) (guard : FlipFlopSizeGuard n m L e)
    (x : Fin n → Bool) (y : Fin m → Bool)
    (q : Fin (matchedBlockOutputBits 64 L) → Bool) (b : Bool) :
    flipFlopStepRuntime L e (List.ofFn x) (List.ofFn y) (List.ofFn q) b =
      List.ofFn (flipFlopStep n m L e x y q b) := by
  obtain ⟨he, hn, hm, hq⟩ := guard
  have left : MatchedBlockRuntimeValid n 24 L e :=
    ⟨by lia, by decide, by lia, hn⟩
  have state : MatchedBlockRuntimeValid (matchedBlockOutputBits 64 L) 24 L e :=
    ⟨by lia, by decide, by lia, hq⟩
  have right : MatchedBlockRuntimeValid m 64 L e :=
    ⟨by lia, by decide, by lia, hm⟩
  cases b <;>
    simp only [flipFlopStepRuntime, flipFlopStep, Bool.false_eq_true, ite_false, ite_true,
      flipFlopLookAheadRuntime_eq n L e left state, pairFst_pair, pairSnd_pair,
      matchedBlockExtractorRuntime_eq_matchedBlockExtractor m 64 L e right]

theorem flipFlopStepRuntime_length_le (L e : Nat) (x y q : List Bool) (b : Bool) :
    (flipFlopStepRuntime L e x y q b).length ≤ matchedBlockOutputBits 64 L :=
  matchedBlockExtractorRuntime_length_le 64 L e y _

theorem flipFlopLookAheadRuntime_mem_FP {L e : List Bool → Nat}
    {x q : List Bool → List Bool} (hL : UnaryFn L) (he : UnaryFn e)
    (hx : x ∈ FP) (hq : q ∈ FP) :
    (fun z => flipFlopLookAheadRuntime (L z) (e z) (x z) (q z)) ∈ FP := by
  polytime [flipFlopLookAheadRuntime, matchedBlockSeedBits]

attribute [local polytime] flipFlopLookAheadRuntime_mem_FP in
theorem flipFlopStepRuntime_mem_FP {L e : List Bool → Nat}
    {x y q : List Bool → List Bool} {b : List Bool → Bool}
    (hL : UnaryFn L) (he : UnaryFn e) (hx : x ∈ FP) (hy : y ∈ FP) (hq : q ∈ FP)
    (hb : FPPred fun z => b z = true) :
    (fun z => flipFlopStepRuntime (L z) (e z) (x z) (y z) (q z) (b z)) ∈ FP := by
  polytime [flipFlopStepRuntime]

theorem flipFlopStepEval_pair (x y q scale error bit : List Bool) :
    flipFlopStepEval (pair (pair x (pair y q)) (pair scale (pair error bit))) =
      flipFlopStepRuntime scale.length error.length x y q (bit[0]?.getD false) := by
  simp only [flipFlopStepEval, pairFst_pair, pairSnd_pair]

theorem flipFlopStepEval_mem_FP : flipFlopStepEval ∈ FP := by
  unfold flipFlopStepEval
  apply flipFlopStepRuntime_mem_FP <;> polytime

end Algebraic.Cutwidth.Extractor.Internal
