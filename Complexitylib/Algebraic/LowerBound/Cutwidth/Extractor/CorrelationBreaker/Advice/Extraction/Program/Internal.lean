/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Advice.Extraction.Program.Defs
public import Complexitylib.Classes.P.Unary.Defs
public import Complexitylib.Classes.P.Defs
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Advice.Program
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Advice.Parameters
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Advice.Truncation
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Scheduled.Matched.Program
import Mathlib.Data.Fin.Tuple.Take
import Complexitylib.Tactic.PolyTime

/-!
# Correctness and uniform bounds for selected advice parameters

The chooser is uniformly unary-computable using only arithmetic and a
ceiling logarithm. Its right-word normalization is polynomial-time and
preserves canonical inputs. The existing bounded advice loop accounts for
every original input, generated parameter, remaining advice, and state
coordinate. Canonical agreement needs no entropy or probability premise.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

open Complexity

theorem adviceErrorExponent_unaryFn {a target : List Bool → Nat}
    (ha : UnaryFn a) (htarget : UnaryFn target) :
    UnaryFn fun z => adviceErrorExponent (a z) (target z) := by
  polytime [adviceErrorExponent]

theorem adviceScale_unaryFn {n a target out : List Bool → Nat}
    (hn : UnaryFn n) (ha : UnaryFn a) (htarget : UnaryFn target) (hout : UnaryFn out) :
    UnaryFn fun z => adviceScale (n z) (a z) (target z) (out z) := by
  polytime [adviceScale]

attribute [local polytime] adviceScale_unaryFn in
theorem adviceSourceEntropy_unaryFn {n a target out : List Bool → Nat}
    (hn : UnaryFn n) (ha : UnaryFn a) (htarget : UnaryFn target) (hout : UnaryFn out) :
    UnaryFn fun z => adviceSourceEntropy (n z) (a z) (target z) (out z) := by
  polytime [adviceSourceEntropy]

theorem adviceSelectedRightWord_length (m : Nat) (y : List Bool) :
    (adviceSelectedRightWord m y).length = m := by
  simp only [adviceSelectedRightWord, List.length_take, List.length_append,
    List.length_replicate]
  exact Nat.min_eq_left (by lia)

theorem adviceSelectedRightWord_eq (m : Nat) (y : List Bool) (length : y.length = m) :
    adviceSelectedRightWord m y = y := by
  rw [adviceSelectedRightWord, ← length, List.take_left]

theorem adviceSelectedRightWord_mem_FP {m : List Bool → Nat} {y : List Bool → List Bool}
    (hm : UnaryFn m) (hy : y ∈ FP) :
    (fun z => adviceSelectedRightWord (m z) (y z)) ∈ FP := by
  polytime [adviceSelectedRightWord]

theorem adviceSelectedCorrelationBreakerRuntime_eq_take (target out : Nat)
    (x y advice : List Bool) :
    adviceSelectedCorrelationBreakerRuntime target out x y advice =
      (adviceCorrelationBreakerRuntime (adviceScale x.length advice.length target out)
        (adviceErrorExponent advice.length target) x
        (adviceSelectedRightWord (adviceSourceEntropy x.length advice.length target out) y)
        advice).take out := by
  unfold adviceSelectedCorrelationBreakerRuntime
  split
  · subst out
    simp
  · rfl

theorem adviceSelectedCorrelationBreakerRuntime_zero (target : Nat)
    (x y advice : List Bool) :
    adviceSelectedCorrelationBreakerRuntime target 0 x y advice = [] := by
  simp only [adviceSelectedCorrelationBreakerRuntime, ite_true]

theorem adviceSelectedCorrelationBreakerRuntime_length (target out : Nat)
    (x y advice : List Bool) :
    (adviceSelectedCorrelationBreakerRuntime target out x y advice).length = out := by
  have guard := adviceParameters_sizeGuard x.length advice.length target out
  have valid : MatchedBlockRuntimeValid x.length 24
      (adviceScale x.length advice.length target out)
      (adviceErrorExponent advice.length target) :=
    ⟨by have := guard.1; lia, by decide, by have := guard.1; lia, guard.2.1⟩
  rw [adviceSelectedCorrelationBreakerRuntime_eq_take, List.length_take,
    adviceCorrelationBreakerRuntime, matchedBlockExtractorRuntime_length, ite_eq_left valid]
  exact Nat.min_eq_left (adviceParameters_output_le x.length advice.length target out)

theorem adviceSelectedCorrelationBreakerRuntime_eq (n target out : Nat)
    (advice : List Bool) (x : Fin n → Bool)
    (y : Fin (adviceSourceEntropy n advice.length target out) → Bool) :
    adviceSelectedCorrelationBreakerRuntime target out (List.ofFn x) (List.ofFn y) advice =
      List.ofFn (adviceTruncatedCorrelationBreaker n
        (adviceSourceEntropy n advice.length target out)
        (adviceScale n advice.length target out) (adviceErrorExponent advice.length target)
        out x y advice) := by
  rw [adviceSelectedCorrelationBreakerRuntime_eq_take, List.length_ofFn,
    adviceSelectedRightWord_eq _ _ (List.length_ofFn (f := y)),
    adviceCorrelationBreakerRuntime_eq _ _ _ _
      (adviceParameters_sizeGuard n advice.length target out)]
  unfold adviceTruncatedCorrelationBreaker
  rw [adviceOutputPrefix_eq_of_le (adviceParameters_output_le n advice.length target out)]
  exact (Fin.ofFn_take_eq_take_ofFn
    (adviceParameters_output_le n advice.length target out) _).symm

theorem adviceSelectedCorrelationBreakerRun_length_le (target out : Nat)
    (x y advice : List Bool) (i : Nat) :
    let n := x.length
    let a := advice.length
    let L := adviceScale n a target out
    let e := adviceErrorExponent a target
    let m := adviceSourceEntropy n a target out
    (encodeAdviceRunState (adviceRun L e x (adviceSelectedRightWord m y) advice i)).length ≤
      4 * n + 2 * m + 2 * L + 2 * e + 2 * a + matchedBlockOutputBits 64 L + 12 := by
  dsimp only
  simpa only [adviceSelectedRightWord_length] using
    adviceRun_length_le (adviceScale x.length advice.length target out)
      (adviceErrorExponent advice.length target) x
      (adviceSelectedRightWord (adviceSourceEntropy x.length advice.length target out) y)
      advice i

attribute [local polytime] adviceErrorExponent_unaryFn adviceScale_unaryFn
  adviceSourceEntropy_unaryFn adviceSelectedRightWord_mem_FP in
theorem adviceSelectedCorrelationBreakerRuntime_mem_FP {target out : List Bool → Nat}
    {x y advice : List Bool → List Bool} (htarget : UnaryFn target) (hout : UnaryFn out)
    (hx : x ∈ FP) (hy : y ∈ FP) (hadvice : advice ∈ FP) :
    (fun z => adviceSelectedCorrelationBreakerRuntime
      (target z) (out z) (x z) (y z) (advice z)) ∈ FP := by
  polytime [adviceSelectedCorrelationBreakerRuntime]

theorem adviceSelectedCorrelationBreakerEval_pair (x y advice targetWord outWord : List Bool) :
    adviceSelectedCorrelationBreakerEval
      (pair (pair x y) (pair advice (pair targetWord outWord))) =
        adviceSelectedCorrelationBreakerRuntime targetWord.length outWord.length x y advice := by
  simp only [adviceSelectedCorrelationBreakerEval, pairFst_pair, pairSnd_pair]

theorem adviceSelectedCorrelationBreakerEval_eq (n target out : Nat)
    (advice : List Bool) (x : Fin n → Bool)
    (y : Fin (adviceSourceEntropy n advice.length target out) → Bool) :
    adviceSelectedCorrelationBreakerEval (pair (pair (List.ofFn x) (List.ofFn y))
      (pair advice (pair (List.replicate target true) (List.replicate out true)))) =
      List.ofFn (adviceTruncatedCorrelationBreaker n
        (adviceSourceEntropy n advice.length target out)
        (adviceScale n advice.length target out) (adviceErrorExponent advice.length target)
        out x y advice) := by
  rw [adviceSelectedCorrelationBreakerEval_pair, List.length_replicate, List.length_replicate]
  exact adviceSelectedCorrelationBreakerRuntime_eq n target out advice x y

theorem adviceSelectedCorrelationBreakerEval_length (z : List Bool) :
    (adviceSelectedCorrelationBreakerEval z).length =
      (pairSnd (pairSnd (pairSnd z))).length :=
  adviceSelectedCorrelationBreakerRuntime_length _ _ _ _ _

theorem adviceSelectedCorrelationBreakerEval_length_le (z : List Bool) :
    (adviceSelectedCorrelationBreakerEval z).length ≤ z.length := by
  rw [adviceSelectedCorrelationBreakerEval_length]
  exact (pairSnd_length_le _).trans ((pairSnd_length_le _).trans (pairSnd_length_le z))

theorem adviceSelectedCorrelationBreakerEval_mem_FP : adviceSelectedCorrelationBreakerEval ∈ FP := by
  unfold adviceSelectedCorrelationBreakerEval
  apply adviceSelectedCorrelationBreakerRuntime_mem_FP <;> polytime

end Algebraic.Cutwidth.Extractor.Internal
