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
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Advice.Program.Internal.Run
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Advice
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.FlipFlop.Program
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Scheduled.Matched.Program
import Complexitylib.Classes.P.Iterate
import Complexitylib.Tactic.PolyTime

/-!
# Exact computation and polynomial time for the complete advice chain

Canonical inputs follow the semantic advice fold and its final extractor.
The complete encoded-state bound discharges the iteration theorem, including
all original inputs and remaining advice. The certificates have no numerical
validity or statistical hypotheses.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

open Complexity

theorem adviceRunStepEval_mem_FP : adviceRunStepEval ∈ FP := by
  have remaining : UnaryFn fun z => (pairFst (pairSnd (pairSnd (pairSnd z)))).length := by
    polytime
  have empty : FPPred fun z => pairFst (pairSnd (pairSnd (pairSnd z))) = [] :=
    (FPPred.eq remaining (UnaryFn.const 0)).of_iff fun _ => List.length_eq_zero_iff
  polytime [adviceRunStepEval, encodeAdviceRunState, adviceRunStep, decodeAdviceRunState]

theorem adviceRun_encoded_mem_FP {L e : List Bool → Nat}
    {x y advice : List Bool → List Bool} (hL : UnaryFn L) (he : UnaryFn e)
    (hx : x ∈ FP) (hy : y ∈ FP) (hadvice : advice ∈ FP) :
    (fun z => encodeAdviceRunState
      (adviceRun (L z) (e z) (x z) (y z) (advice z) (advice z).length)) ∈ FP := by
  have start : (fun z => encodeAdviceRunState
      (adviceRunInitial (L z) (e z) (x z) (y z) (advice z))) ∈ FP := by
    polytime [encodeAdviceRunState, adviceRunInitial, adviceInitialWord, matchedBlockOutputBits]
  have width : UnaryFn fun z =>
      4 * (x z).length + 2 * (y z).length + 2 * L z + 2 * e z +
        2 * (advice z).length + matchedBlockOutputBits 64 (L z) + 12 := by
    polytime [matchedBlockOutputBits]
  have loop := iterate_mem_FP adviceRunStepEval_mem_FP start hadvice width.mem_FP
    (fun z i _ => by
      rw [adviceRunStepEval_iterate, List.length_replicate]
      exact adviceRun_length_le (L z) (e z) (x z) (y z) (advice z) i)
  refine mem_FP_of_eq loop fun z => ?_
  exact adviceRunStepEval_iterate _ _

theorem adviceCorrelationBreakerRuntime_mem_FP {L e : List Bool → Nat}
    {x y advice : List Bool → List Bool} (hL : UnaryFn L) (he : UnaryFn e)
    (hx : x ∈ FP) (hy : y ∈ FP) (hadvice : advice ∈ FP) :
    (fun z => adviceCorrelationBreakerRuntime (L z) (e z) (x z) (y z) (advice z)) ∈ FP := by
  have loop := adviceRun_encoded_mem_FP hL he hx hy hadvice
  have projected : (fun z => pairSnd (pairSnd (pairSnd (pairSnd
      (encodeAdviceRunState
        (adviceRun (L z) (e z) (x z) (y z) (advice z) (advice z).length)))))) ∈ FP := by
    polytime
  have current : (fun z =>
      (adviceRun (L z) (e z) (x z) (y z) (advice z) (advice z).length).q) ∈ FP := by
    simpa only [encodeAdviceRunState, pairSnd_pair] using projected
  polytime [adviceCorrelationBreakerRuntime, matchedBlockSeedBits]

theorem adviceRuntimeFold_eq (n m L e : Nat) (guard : FlipFlopSizeGuard n m L e)
    (x : Fin n → Bool) (y : Fin m → Bool)
    (q : Fin (matchedBlockOutputBits 64 L) → Bool) (advice : List Bool) :
    advice.foldl (flipFlopStepRuntime L e (List.ofFn x) (List.ofFn y)) (List.ofFn q) =
      List.ofFn (adviceFold n m L e x y q advice) := by
  induction advice generalizing q with
  | nil => rfl
  | cons bit rest ih =>
    rw [List.foldl_cons, flipFlopStepRuntime_eq n m L e guard,
      adviceFold_cons]
    exact ih _

theorem adviceRun_eq_adviceFold (n m L e : Nat) (guard : FlipFlopSizeGuard n m L e)
    (x : Fin n → Bool) (y : Fin m → Bool) (advice : List Bool) :
    adviceRun L e (List.ofFn x) (List.ofFn y) advice advice.length =
      ⟨List.ofFn x, List.ofFn y, L, e, [],
        List.ofFn (adviceFold n m L e x y (adviceInitialState m L y) advice)⟩ := by
  rw [adviceRun_fold, ← adviceInitialState_ofFn,
    adviceRuntimeFold_eq n m L e guard]

theorem adviceCorrelationBreakerRuntime_eq (n m L e : Nat)
    (guard : FlipFlopSizeGuard n m L e) (x : Fin n → Bool) (y : Fin m → Bool)
    (advice : List Bool) :
    adviceCorrelationBreakerRuntime L e (List.ofFn x) (List.ofFn y) advice =
      List.ofFn (adviceCorrelationBreaker n m L e x y advice) := by
  have left : MatchedBlockRuntimeValid n 24 L e :=
    ⟨by have := guard.1; lia, by decide, by have := guard.1; lia, guard.2.1⟩
  unfold adviceCorrelationBreakerRuntime
  rw [adviceRun_eq_adviceFold n m L e guard]
  change matchedBlockExtractorRuntime 24 L e (List.ofFn x)
    ((List.ofFn (adviceFold n m L e x y (adviceInitialState m L y) advice)).take
      (matchedBlockSeedBits L)) = _
  rw [← flipFlopSeedPrefix_ofFn]
  exact matchedBlockExtractorRuntime_eq_matchedBlockExtractor n 24 L e left x _

theorem adviceCorrelationBreakerRuntime_length_le (L e : Nat) (x y advice : List Bool) :
    (adviceCorrelationBreakerRuntime L e x y advice).length ≤ matchedBlockSeedBits L := by
  rw [adviceCorrelationBreakerRuntime, matchedBlockExtractorRuntime_length]
  split <;> simp only [matchedBlockSeedBits, le_refl, Nat.zero_le]

theorem adviceCorrelationBreakerEval_pair (x y scale error advice : List Bool) :
    adviceCorrelationBreakerEval (pair (pair x y) (pair scale (pair error advice))) =
      adviceCorrelationBreakerRuntime scale.length error.length x y advice := by
  simp only [adviceCorrelationBreakerEval, pairFst_pair, pairSnd_pair]

theorem adviceCorrelationBreakerEval_mem_FP : adviceCorrelationBreakerEval ∈ FP := by
  unfold adviceCorrelationBreakerEval
  apply adviceCorrelationBreakerRuntime_mem_FP <;> polytime

end Algebraic.Cutwidth.Extractor.Internal
