/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Scheduled.Program.Defs
public import Complexitylib.Classes.P.Defs
public import Complexitylib.Classes.P.Unary.Defs
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Scheduled.Run
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Scheduled.State.Parameters
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Parameters.Explicit
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.OneShot.Block.Program
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Parameters.Explicit.Unary
import Complexitylib.Classes.P.StringAccess
import Complexitylib.Tactic.PolyTime

/-!
# Polynomial-time computation of the complete scheduled extractor

The final shared extraction stage composes with the certified complete block
loop. The total parameter generator supplies every capacity, reserve, and
bounded-power obligation for arbitrary runtime inputs. The result is one
uniform polynomial-time program, including parameter generation and all
internal levels, without a caller-supplied validity premise.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

open Complexity

theorem scheduledBlockFinishEval_encode (E ell : Nat) (state : ScheduledBlockRunState) :
    scheduledBlockFinishEval (pair (encodeScheduledBlockRun E state) (List.replicate ell true)) =
      scheduledBlockFinish E ell state := by
  simp only [scheduledBlockFinishEval, encodeScheduledBlockRun, encodeScheduledBlockState,
    scheduledBlockFinish, pairFst_pair, pairSnd_pair, List.length_replicate]

theorem scheduledBlockFinishEval_mem_FP : scheduledBlockFinishEval ∈ FP := by
  unfold scheduledBlockFinishEval oneShotCondenserExponent
  polytime

theorem scheduledBlockExtractorBits_length (n h Q E ell : Nat) (source seeds : List Bool) :
    (scheduledBlockExtractorBits n h Q E ell source seeds).length = 2 ^ h * ell := by
  simp only [scheduledBlockExtractorBits, scheduledBlockFinish, oneShotBlockExtractorBits_length,
    List.length_replicate, scheduledBlockRun_count]

theorem scheduledBlockExtractorBits_mem_FP {n h Q E ell : List Bool → Nat}
    {source seeds : List Bool → List Bool} (hn : UnaryFn n)
    (hentropy : UnaryFn fun z => recursiveBlockEntropy (h z) (Q z) 0)
    (hh : UnaryFn h) (hE : UnaryFn E) (hell : UnaryFn ell)
    (hsource : source ∈ FP) (hseeds : seeds ∈ FP) (positive : ∀ z, 0 < Q z)
    (budget : ∀ z, 3 * (24 * explicitCondenserBudget
      (scheduledBlockInitialWidth (n z) (h z) (Q z) (E z))
      (recursiveBlockEntropy (h z) (Q z) 0) (E z)) + 6 * E z ≤ 2 * Q z) :
    (fun z => scheduledBlockExtractorBits (n z) (h z) (Q z) (E z) (ell z)
      (source z) (seeds z)) ∈ FP := by
  have loop := scheduledBlockRun_mem_FP (n := n) (h := h) (Q := Q) (E := E)
    (source := source) (seeds := seeds) hn hentropy hh hE hsource hseeds positive budget
  have finished := mem_FP_comp (mem_FP_pair loop hell.mem_FP) scheduledBlockFinishEval_mem_FP
  simpa only [Function.comp_def, scheduledBlockFinishEval_encode, scheduledBlockExtractorBits]
    using finished

theorem scheduledBlockExtractorRuntime_mem_FP {requested e : List Bool → Nat}
    {source seeds : List Bool → List Bool} (hrequested : UnaryFn requested) (he : UnaryFn e)
    (hsource : source ∈ FP) (hseeds : seeds ∈ FP) :
    (fun z => scheduledBlockExtractorRuntime (requested z) (e z) (source z) (seeds z)) ∈ FP := by
  unfold scheduledBlockExtractorRuntime
  apply scheduledBlockExtractorBits_mem_FP
  · polytime
  · change UnaryFn fun z => scheduledBlockInitialEntropy
      (source z).length (requested z) (e z)
    polytime
  · polytime
  · polytime
  · polytime
  · exact hsource
  · exact hseeds
  · intro z
    exact recursiveBlockReserve_pos _ _
  · intro z
    exact scheduledBlockRuntime_reserve_budget (source z).length (requested z) (e z)

theorem scheduledBlockExtractorEval_pair (source seeds requested error : List Bool) :
    scheduledBlockExtractorEval (pair (pair source seeds) (pair requested error)) =
      scheduledBlockExtractorRuntime requested.length error.length source seeds := by
  simp only [scheduledBlockExtractorEval, pairFst_pair, pairSnd_pair]

theorem scheduledBlockExtractorRuntime_of_depth_le (requested e : Nat)
    (source seeds : List Bool) (depth : requested ≤ Nat.clog 2 (source.length + 1)) :
    scheduledBlockExtractorRuntime requested e source seeds =
      scheduledBlockExtractorBits source.length requested
        (recursiveBlockReserve (Nat.clog 2 (source.length + 1)) (e + requested + 2))
        (e + requested + 2) (Nat.clog 2 (source.length + 1)) source seeds := by
  simp only [scheduledBlockExtractorRuntime, scheduledBlockLeafReserve,
    scheduledBlockErrorExponent, scheduledBlockDepth, scheduledBlockInputLog, min_eq_left depth]

theorem scheduledBlockExtractorEval_mem_FP : scheduledBlockExtractorEval ∈ FP := by
  unfold scheduledBlockExtractorEval
  apply scheduledBlockExtractorRuntime_mem_FP <;> polytime

end Algebraic.Cutwidth.Extractor.Internal
