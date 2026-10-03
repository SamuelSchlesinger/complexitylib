/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Scheduled.Matched.Program.Defs
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Scheduled.Matched.Defs
public import Complexitylib.Classes.P.Defs
public import Complexitylib.Classes.P.Unary.Defs
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Scheduled.Program
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Scheduled.Matched
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Scheduled.State
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Parameters.Explicit
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Encoding.Explicit.Pair.Unary
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Encoding.Explicit.Pair.Splitting
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.OneShot.Parameters
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Parameters.Explicit.Unary
import Complexitylib.Classes.P.StringAccess
import Complexitylib.Tactic.PolyTime
import Mathlib.Tactic.Linarith

/-!
# Uniform computation of the shared-scale matched extractor

Bounded numerical-state iteration computes every actual width and its seed
cost. A finite sum gives the exact total seed prefix before the unchanged
payload program runs. Safe parameters certify this complete computation on
all inputs; on the valid branch they equal the supplied parameters. Depth
is bounded by 64 when generating powers, and every intermediate numerical
and payload state uses the existing global reserve bound.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

open Complexity

private theorem scheduleNumbers_unaryFn {initial h Q E count : List Bool → Nat}
    (hinitial : UnaryFn initial)
    (hentropy : UnaryFn fun z => recursiveBlockEntropy (h z) (Q z) 0)
    (hE : UnaryFn E) (hcount : UnaryFn count)
    (capacity : ∀ z, recursiveBlockEntropy (h z) (Q z) 0 ≤ initial z)
    (budget : ∀ z, 3 * (24 * explicitCondenserBudget (initial z)
      (recursiveBlockEntropy (h z) (Q z) 0) (E z)) + 6 * E z ≤ 2 * Q z)
    (levels : ∀ z, count z ≤ h z) :
    (UnaryFn fun z => recursiveBlockWidth (initial z) (h z) (Q z) (E z) (count z)) ∧
      UnaryFn fun z => recursiveBlockEntropy (h z) (Q z) (count z) := by
  let state := fun z => encodeScheduledBlockState (E z)
    (recursiveBlockWidth (initial z) (h z) (Q z) (E z) (count z),
      recursiveBlockEntropy (h z) (Q z) (count z))
  have compiled : state ∈ FP :=
    scheduledBlockState_mem_FP hinitial hentropy hE hcount capacity budget levels
  constructor
  · have width : UnaryFn fun z => (pairFst (pairFst (state z))).length := by polytime
    exact width.of_eq fun z => by
      simp only [state, encodeScheduledBlockState, pairFst_pair, List.length_replicate]
  · have entropy : UnaryFn fun z => (pairSnd (pairFst (state z))).length := by polytime
    exact entropy.of_eq fun z => by
      simp only [state, encodeScheduledBlockState, pairFst_pair, pairSnd_pair, List.length_replicate]

/-- Bounded schedule iteration computes the exact seed width at any certified depth. -/
theorem scheduledSeedBits_unaryFn {n h Q E ell : List Bool → Nat}
    (hn : UnaryFn n) (hh : UnaryFn h)
    (hentropy : UnaryFn fun z => recursiveBlockEntropy (h z) (Q z) 0)
    (hE : UnaryFn E) (hell : UnaryFn ell)
    (budget : ∀ z, 3 * (24 * explicitCondenserBudget
      (scheduledBlockInitialWidth (n z) (h z) (Q z) (E z))
      (recursiveBlockEntropy (h z) (Q z) 0) (E z)) + 6 * E z ≤ 2 * Q z) :
    UnaryFn fun z => scheduledBlockSeedBits (n z) (h z) (Q z) (E z) (ell z) := by
  let initial := fun z => scheduledBlockInitialWidth (n z) (h z) (Q z) (E z)
  have hinitial : UnaryFn initial := by
    unfold initial scheduledBlockInitialWidth
    polytime
  have capacity : ∀ z, recursiveBlockEntropy (h z) (Q z) 0 ≤ initial z :=
    fun z => explicitCondenserHalfWidth_capacity (n z)
      (recursiveBlockEntropy (h z) (Q z) 0) (E z) (by decide : 0 < 1)
  have last := scheduleNumbers_unaryFn hinitial hentropy hE hh capacity budget (fun _ => le_rfl)
  have levels := scheduleNumbers_unaryFn hinitial.lift hentropy.lift hE.lift
    (UnaryFn.index.min hh.lift) (fun w => capacity (pairFst w))
    (fun w => budget (pairFst w)) (fun w => min_le_right _ _)
  have step : UnaryFn fun w => sparseFieldBits 3 (explicitCondenserBudget
      (recursiveBlockWidth (initial (pairFst w)) (h (pairFst w)) (Q (pairFst w))
        (E (pairFst w)) (min (pairSnd w).length (h (pairFst w))))
      (recursiveBlockEntropy (h (pairFst w)) (Q (pairFst w))
        (min (pairSnd w).length (h (pairFst w)))) (E (pairFst w))) := by
    have width := levels.1
    have entropy := levels.2
    polytime
  have sum := hh.sum step
  have sumExact : UnaryFn fun z => (Finset.range (h z)).sum
      (recursiveBlockSeedWidth (initial z) (h z) (Q z) (E z)) := by
    refine sum.of_eq fun z => ?_
    apply Finset.sum_congr rfl
    intro i hi
    simp only [pairFst_pair, pairSnd_pair, List.length_replicate,
      min_eq_left (Nat.le_of_lt (Finset.mem_range.mp hi)), recursiveBlockSeedWidth]
  unfold scheduledBlockSeedBits
  have width := last.1
  change UnaryFn fun z => sparseFieldBits 1
    (explicitCondenserBudget (n z) (recursiveBlockEntropy (h z) (Q z) 0) (E z)) +
      (Finset.range (h z)).sum (recursiveBlockSeedWidth (initial z) (h z) (Q z) (E z)) +
      (2 * 3 ^ oneShotCondenserExponent
        (recursiveBlockWidth (initial z) (h z) (Q z) (E z) (h z)) (ell z) (E z) +
       2 * 3 ^ oneShotHashExponent
        (recursiveBlockWidth (initial z) (h z) (Q z) (E z) (h z)) (ell z) (E z))
  polytime

theorem matchedBlockExtractorRuntime_of_valid (h L e : Nat) (source seeds : List Bool)
    (valid : MatchedBlockRuntimeValid source.length h L e) :
    matchedBlockExtractorRuntime h L e source seeds =
      scheduledBlockExtractorBits source.length h (recursiveBlockReserve L (e + h + 2))
        (e + h + 2) L source (seeds.take (scheduledBlockSeedBits source.length h
          (recursiveBlockReserve L (e + h + 2)) (e + h + 2) L)) := by
  simp only [matchedBlockExtractorRuntime, ite_eq_left valid]

theorem matchedBlockExtractorRuntime_of_not_valid (h L e : Nat) (source seeds : List Bool)
    (invalid : ¬ MatchedBlockRuntimeValid source.length h L e) :
    matchedBlockExtractorRuntime h L e source seeds = [] := by
  simp only [matchedBlockExtractorRuntime, ite_eq_right invalid]

theorem matchedBlockExtractorRuntime_length (h L e : Nat) (source seeds : List Bool) :
    (matchedBlockExtractorRuntime h L e source seeds).length =
      if MatchedBlockRuntimeValid source.length h L e then 2 ^ h * L else 0 := by
  by_cases valid : MatchedBlockRuntimeValid source.length h L e
  · rw [matchedBlockExtractorRuntime_of_valid _ _ _ _ _ valid,
      scheduledBlockExtractorBits_length, ite_eq_left valid]
  · rw [matchedBlockExtractorRuntime_of_not_valid _ _ _ _ _ valid, ite_eq_right valid]
    rfl

theorem matchedBlockExtractorRuntime_length_le (h L e : Nat) (source seeds : List Bool) :
    (matchedBlockExtractorRuntime h L e source seeds).length ≤ 2 ^ 64 * L := by
  rw [matchedBlockExtractorRuntime_length]
  split_ifs with valid
  · exact Nat.mul_le_mul_right L (Nat.pow_le_pow_right (by decide : 0 < 2) valid.2.1)
  · exact Nat.zero_le _

theorem matchedBlockRuntimeValid_fpPred {n h L e : List Bool → Nat}
    (hn : UnaryFn n) (hh : UnaryFn h) (hL : UnaryFn L) (he : UnaryFn e) :
    FPPred fun z => MatchedBlockRuntimeValid (n z) (h z) (L z) (e z) := by
  unfold MatchedBlockRuntimeValid
  polytime

theorem matchedBlockExtractorRuntime_mem_FP {h L e : List Bool → Nat}
    {source seeds : List Bool → List Bool} (hh : UnaryFn h) (hL : UnaryFn L) (he : UnaryFn e)
    (hsource : source ∈ FP) (hseeds : seeds ∈ FP) :
    (fun z => matchedBlockExtractorRuntime (h z) (L z) (e z) (source z) (seeds z)) ∈ FP := by
  let depth := fun z => min (h z) 64
  let scale := fun z => max 64 (max (L z) (Nat.clog 2 ((source z).length + 1)))
  let error := fun z => e z + depth z + 2
  let reserve := fun z => recursiveBlockReserve (scale z) (error z)
  have hn : UnaryFn fun z => (source z).length := by polytime
  have hdepth : UnaryFn depth := by unfold depth; polytime
  have hscale : UnaryFn scale := by unfold scale; polytime
  have herror : UnaryFn error := by unfold error; polytime
  have hreserve : UnaryFn reserve := by unfold reserve recursiveBlockReserve; polytime
  have power : UnaryFn fun z => 4 ^ depth z :=
    (UnaryFn.const 4).pow_of_le hdepth (UnaryFn.const (4 ^ 64)) fun z =>
      Nat.pow_le_pow_right (by decide : 0 < 4) (min_le_right _ _)
  have entropy : UnaryFn fun z => recursiveBlockEntropy (depth z) (reserve z) 0 := by
    simpa only [recursiveBlockEntropy, Nat.sub_zero] using power.mul hreserve
  have budget : ∀ z, 3 * (24 * explicitCondenserBudget
      (scheduledBlockInitialWidth (source z).length (depth z) (reserve z) (error z))
      (recursiveBlockEntropy (depth z) (reserve z) 0) (error z)) +
        6 * error z ≤ 2 * reserve z := by
    intro z
    apply recursiveBlockReserve_budget (source z).length (scale z) (error z) (depth z)
    · exact (le_max_right _ _).trans (le_max_right _ _)
    · exact (min_le_right _ _).trans (le_max_left _ _)
  have seedWidth := scheduledSeedBits_unaryFn hn hdepth entropy herror hscale budget
  have trimmed : (fun z => (seeds z).take
      (scheduledBlockSeedBits (source z).length (depth z) (reserve z) (error z) (scale z))) ∈ FP :=
    take_mem_FP hseeds seedWidth
  have compiled := scheduledBlockExtractorBits_mem_FP hn entropy hdepth herror hscale
    hsource trimmed (fun z => recursiveBlockReserve_pos (scale z) (error z)) budget
  have guard := matchedBlockRuntimeValid_fpPred hn hh hL he
  have selected := guard.ite_mem_FP compiled (constFn_mem_FP [])
  refine mem_FP_of_eq selected fun z => ?_
  by_cases valid : MatchedBlockRuntimeValid (source z).length (h z) (L z) (e z)
  · rw [ite_eq_left valid, matchedBlockExtractorRuntime_of_valid _ _ _ _ _ valid]
    have hdepthEq : depth z = h z := min_eq_left valid.2.1
    have hscaleEq : scale z = L z := by
      simp only [scale, max_eq_left valid.2.2.2, max_eq_right valid.1]
    simp only [reserve, error, hdepthEq, hscaleEq]
  · rw [ite_eq_right valid, matchedBlockExtractorRuntime_of_not_valid _ _ _ _ _ valid]

theorem matchedBlockExtractorEval_pair (source seeds depth scale error : List Bool) :
    matchedBlockExtractorEval (pair (pair source seeds) (pair depth (pair scale error))) =
      matchedBlockExtractorRuntime depth.length scale.length error.length source seeds := by
  simp only [matchedBlockExtractorEval, pairFst_pair, pairSnd_pair]

theorem matchedBlockExtractorEval_mem_FP : matchedBlockExtractorEval ∈ FP := by
  unfold matchedBlockExtractorEval
  apply matchedBlockExtractorRuntime_mem_FP <;> polytime

theorem matchedBlockExtractorRuntime_eq_matchedBlockExtractor (n h L e : Nat)
    (valid : MatchedBlockRuntimeValid n h L e) (x : Fin n → Bool)
    (seed : Fin (matchedBlockSeedBits L) → Bool) :
    matchedBlockExtractorRuntime h L e (List.ofFn x) (List.ofFn seed) =
      List.ofFn (matchedBlockExtractor n h L e x seed) := by
  rw [matchedBlockExtractorRuntime_of_valid h L e _ _ (by simpa using valid)]
  simp only [List.length_ofFn]
  exact (matchedBlockExtractor_ofFn_take n h L e
    (matchedBlockExtractor_seedBits_le n h L e valid.2.2.2 valid.1 valid.2.1 valid.2.2.1)
    x seed).symm

theorem matchedBlockExtractorRuntime_append_eq_matchedBlockExtractor (n h L e : Nat)
    (valid : MatchedBlockRuntimeValid n h L e) (x : Fin n → Bool)
    (seed : Fin (matchedBlockSeedBits L) → Bool) (tail : List Bool) :
    matchedBlockExtractorRuntime h L e (List.ofFn x) (List.ofFn seed ++ tail) =
      List.ofFn (matchedBlockExtractor n h L e x seed) := by
  rw [matchedBlockExtractorRuntime_of_valid h L e _ _ (by simpa using valid)]
  simp only [List.length_ofFn]
  have size := matchedBlockExtractor_seedBits_le n h L e
    valid.2.2.2 valid.1 valid.2.1 valid.2.2.1
  rw [List.take_append_of_le_length (by simpa using size)]
  exact (matchedBlockExtractor_ofFn_take n h L e size x seed).symm

end Algebraic.Cutwidth.Extractor.Internal
