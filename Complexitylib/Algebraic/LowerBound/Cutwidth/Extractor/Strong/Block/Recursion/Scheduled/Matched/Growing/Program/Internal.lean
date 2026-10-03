/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Scheduled.Matched.Growing.Program.Defs
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Scheduled.Matched.Defs
public import Complexitylib.Classes.P.Defs
public import Complexitylib.Classes.P.Unary.Defs
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Scheduled.Program
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Scheduled.Matched.Growing
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Scheduled.Matched
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Scheduled.Matched.Program.Internal
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Parameters.Explicit
import Complexitylib.Classes.P.StringAccess
import Complexitylib.Classes.P.Unary
import Complexitylib.Tactic.PolyTime
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Polynomial resource bounds for growing-depth matched extraction

The leaf count is at most `2^65 * (t+1)`. Its square bounds the initial
entropy factor, so unary generation of every parameter remains polynomial.
For the total FP proof, a safe enlarged scale pays the existing global
reserve on every input. On valid inputs it equals the requested scale.
The existing numerical-state and payload certificates bound all intermediate
states; a computed exact seed prefix prevents surplus bits entering the hash.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

open Complexity

private theorem pow_clog_two_le (t : Nat) : 2 ^ Nat.clog 2 (t + 1) ≤ 2 * (t + 1) := by
  by_cases zero : t = 0
  · simp [zero]
  have larger : 1 < t + 1 := by lia
  have lower := Nat.pow_pred_clog_lt_self (by decide : 1 < 2) larger
  have positive := Nat.clog_pos (by decide : 1 < 2) larger
  have exponent : (Nat.clog 2 (t + 1)).pred + 1 = Nat.clog 2 (t + 1) :=
    Nat.succ_pred_eq_of_pos positive
  calc
    2 ^ Nat.clog 2 (t + 1) = 2 ^ (Nat.clog 2 (t + 1)).pred * 2 := by
      rw [← pow_succ, exponent]
    _ ≤ 2 * (t + 1) := by lia

theorem growingMatchedBlockDepth_pow_le (t : Nat) :
    2 ^ growingMatchedBlockDepth t ≤ 2 ^ 65 * (t + 1) := by
  calc
    2 ^ growingMatchedBlockDepth t = 2 ^ Nat.clog 2 (t + 1) * 2 ^ 64 :=
      pow_add _ _ _
    _ ≤ (2 * (t + 1)) * 2 ^ 64 := Nat.mul_le_mul_right _ (pow_clog_two_le t)
    _ = 2 ^ 65 * (t + 1) := by rw [show 65 = 64 + 1 from rfl, pow_succ]; ring

theorem growingMatchedBlockDepth_pow_four_le (t : Nat) :
    4 ^ growingMatchedBlockDepth t ≤ (2 ^ 65 * (t + 1)) ^ 2 := by
  calc
    4 ^ growingMatchedBlockDepth t = (2 ^ growingMatchedBlockDepth t) ^ 2 := by
      rw [← pow_mul, Nat.mul_comm, pow_mul]
      rfl
    _ ≤ (2 ^ 65 * (t + 1)) ^ 2 := Nat.pow_le_pow_left (growingMatchedBlockDepth_pow_le t) 2

theorem growingMatchedBlockDepth_unaryFn {t : List Bool → Nat} (ht : UnaryFn t) :
    UnaryFn fun z => growingMatchedBlockDepth (t z) := by
  unfold growingMatchedBlockDepth
  polytime

theorem growingMatchedBlockDepth_pow_unaryFn {t : List Bool → Nat} (ht : UnaryFn t) :
    UnaryFn fun z => 2 ^ growingMatchedBlockDepth (t z) := by
  have bound : UnaryFn fun z => 2 ^ 65 * (t z + 1) := by polytime
  exact (UnaryFn.const 2).pow_of_le (growingMatchedBlockDepth_unaryFn ht) bound
    fun z => growingMatchedBlockDepth_pow_le (t z)

theorem growingMatchedBlockRuntimeValid_fpPred {n t L e : List Bool → Nat}
    (hn : UnaryFn n) (ht : UnaryFn t) (hL : UnaryFn L) (he : UnaryFn e) :
    FPPred fun z => GrowingMatchedBlockRuntimeValid (n z) (t z) (L z) (e z) := by
  have depth := growingMatchedBlockDepth_unaryFn ht
  unfold GrowingMatchedBlockRuntimeValid
  polytime

theorem growingMatchedBlockExtractorRuntime_of_valid (t L e : Nat) (source seeds : List Bool)
    (valid : GrowingMatchedBlockRuntimeValid source.length t L e) :
    growingMatchedBlockExtractorRuntime t L e source seeds =
      let h := growingMatchedBlockDepth t
      scheduledBlockExtractorBits source.length h (recursiveBlockReserve L (e + h + 2))
        (e + h + 2) L source (seeds.take (scheduledBlockSeedBits source.length h
          (recursiveBlockReserve L (e + h + 2)) (e + h + 2) L)) := by
  simp only [growingMatchedBlockExtractorRuntime, ite_eq_left valid]

theorem growingMatchedBlockExtractorRuntime_of_not_valid (t L e : Nat) (source seeds : List Bool)
    (invalid : ¬ GrowingMatchedBlockRuntimeValid source.length t L e) :
    growingMatchedBlockExtractorRuntime t L e source seeds = [] := by
  simp only [growingMatchedBlockExtractorRuntime, ite_eq_right invalid]

theorem growingMatchedBlockExtractorRuntime_length (t L e : Nat) (source seeds : List Bool) :
    (growingMatchedBlockExtractorRuntime t L e source seeds).length =
      if GrowingMatchedBlockRuntimeValid source.length t L e then
        2 ^ growingMatchedBlockDepth t * L else 0 := by
  by_cases valid : GrowingMatchedBlockRuntimeValid source.length t L e
  · rw [growingMatchedBlockExtractorRuntime_of_valid _ _ _ _ _ valid,
      scheduledBlockExtractorBits_length, ite_eq_left valid]
  · rw [growingMatchedBlockExtractorRuntime_of_not_valid _ _ _ _ _ valid, ite_eq_right valid]
    rfl

theorem growingMatchedBlockExtractorRuntime_length_le (t L e : Nat) (source seeds : List Bool) :
    (growingMatchedBlockExtractorRuntime t L e source seeds).length ≤ 2 ^ 65 * (t + 1) * L := by
  rw [growingMatchedBlockExtractorRuntime_length]
  split_ifs
  · exact Nat.mul_le_mul_right L (growingMatchedBlockDepth_pow_le t)
  · exact Nat.zero_le _

theorem growingMatchedBlockExtractorRuntime_mem_FP {t L e : List Bool → Nat}
    {source seeds : List Bool → List Bool} (ht : UnaryFn t) (hL : UnaryFn L) (he : UnaryFn e)
    (hsource : source ∈ FP) (hseeds : seeds ∈ FP) :
    (fun z => growingMatchedBlockExtractorRuntime (t z) (L z) (e z) (source z) (seeds z)) ∈ FP := by
  let depth := fun z => growingMatchedBlockDepth (t z)
  let scale := fun z => max (depth z) (max (L z) (Nat.clog 2 ((source z).length + 1)))
  let error := fun z => e z + depth z + 2
  let reserve := fun z => recursiveBlockReserve (scale z) (error z)
  have hn : UnaryFn fun z => (source z).length := by polytime
  have hdepth : UnaryFn depth := growingMatchedBlockDepth_unaryFn ht
  have hscale : UnaryFn scale := by unfold scale; polytime
  have herror : UnaryFn error := by unfold error; polytime
  have hreserve : UnaryFn reserve := by unfold reserve recursiveBlockReserve; polytime
  have powerBound : UnaryFn fun z => (2 ^ 65 * (t z + 1)) ^ 2 := by polytime
  have power : UnaryFn fun z => 4 ^ depth z :=
    (UnaryFn.const 4).pow_of_le hdepth powerBound fun z =>
      growingMatchedBlockDepth_pow_four_le (t z)
  have entropy : UnaryFn fun z => recursiveBlockEntropy (depth z) (reserve z) 0 := by
    simpa only [recursiveBlockEntropy, Nat.sub_zero] using power.mul hreserve
  have budget : ∀ z, 3 * (24 * explicitCondenserBudget
      (scheduledBlockInitialWidth (source z).length (depth z) (reserve z) (error z))
      (recursiveBlockEntropy (depth z) (reserve z) 0) (error z)) +
        6 * error z ≤ 2 * reserve z := by
    intro z
    apply recursiveBlockReserve_budget (source z).length (scale z) (error z) (depth z)
    · exact (le_max_right _ _).trans (le_max_right _ _)
    · exact le_max_left _ _
  have seedWidth := scheduledSeedBits_unaryFn hn hdepth entropy herror hscale budget
  have trimmed : (fun z => (seeds z).take
      (scheduledBlockSeedBits (source z).length (depth z) (reserve z) (error z) (scale z))) ∈ FP :=
    take_mem_FP hseeds seedWidth
  have compiled := scheduledBlockExtractorBits_mem_FP hn entropy hdepth herror hscale
    hsource trimmed (fun z => recursiveBlockReserve_pos (scale z) (error z)) budget
  have guard := growingMatchedBlockRuntimeValid_fpPred hn ht hL he
  have selected := guard.ite_mem_FP compiled (constFn_mem_FP [])
  refine mem_FP_of_eq selected fun z => ?_
  by_cases valid : GrowingMatchedBlockRuntimeValid (source z).length (t z) (L z) (e z)
  · rw [ite_eq_left valid, growingMatchedBlockExtractorRuntime_of_valid _ _ _ _ _ valid]
    have depth_le : depth z ≤ L z := by have bound := valid.2.1; dsimp only [depth]; lia
    have scale_eq : scale z = L z := by
      simp only [scale, max_eq_left valid.1, max_eq_right depth_le]
    simp only [reserve, error, depth, scale_eq]
  · rw [ite_eq_right valid, growingMatchedBlockExtractorRuntime_of_not_valid _ _ _ _ _ valid]

theorem growingMatchedBlockExtractorEval_pair (source seeds parameter scale error : List Bool) :
    growingMatchedBlockExtractorEval
      (pair (pair source seeds) (pair parameter (pair scale error))) =
      growingMatchedBlockExtractorRuntime parameter.length scale.length error.length source seeds := by
  simp only [growingMatchedBlockExtractorEval, pairFst_pair, pairSnd_pair]

theorem growingMatchedBlockExtractorEval_mem_FP : growingMatchedBlockExtractorEval ∈ FP := by
  unfold growingMatchedBlockExtractorEval
  apply growingMatchedBlockExtractorRuntime_mem_FP <;> polytime

theorem growingMatchedBlockExtractorEval_length_le (z : List Bool) :
    (growingMatchedBlockExtractorEval z).length ≤ 2 ^ 65 * (z.length + 1) ^ 2 := by
  have parameter := (pairFst_length_le (pairSnd z)).trans (pairSnd_length_le z)
  have scale := (pairFst_length_le (pairSnd (pairSnd z))).trans
    ((pairSnd_length_le (pairSnd z)).trans (pairSnd_length_le z))
  calc
    (growingMatchedBlockExtractorEval z).length ≤
        2 ^ 65 * ((pairFst (pairSnd z)).length + 1) *
          (pairFst (pairSnd (pairSnd z))).length :=
      growingMatchedBlockExtractorRuntime_length_le _ _ _ _ _
    _ ≤ 2 ^ 65 * (z.length + 1) * (z.length + 1) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ (Nat.add_le_add_right parameter 1))
        (scale.trans (Nat.le_succ _))
    _ = 2 ^ 65 * (z.length + 1) ^ 2 := by ring

theorem growingMatchedBlockExtractorRuntime_eq_matchedBlockExtractor (n t L e : Nat)
    (valid : GrowingMatchedBlockRuntimeValid n t L e) (x : Fin n → Bool)
    (seed : Fin (matchedBlockSeedBits L) → Bool) :
    growingMatchedBlockExtractorRuntime t L e (List.ofFn x) (List.ofFn seed) =
      List.ofFn (matchedBlockExtractor n (growingMatchedBlockDepth t) L e x seed) := by
  rw [growingMatchedBlockExtractorRuntime_of_valid t L e _ _ (by simpa using valid)]
  simp only [List.length_ofFn]
  exact (matchedBlockExtractor_ofFn_take n (growingMatchedBlockDepth t) L e
    (matchedBlockExtractor_growing_seedBits_le n (growingMatchedBlockDepth t) L e
      valid.1 valid.2.1 valid.2.2) x seed).symm

theorem growingMatchedBlockExtractorRuntime_append_eq_matchedBlockExtractor (n t L e : Nat)
    (valid : GrowingMatchedBlockRuntimeValid n t L e) (x : Fin n → Bool)
    (seed : Fin (matchedBlockSeedBits L) → Bool) (tail : List Bool) :
    growingMatchedBlockExtractorRuntime t L e (List.ofFn x) (List.ofFn seed ++ tail) =
      List.ofFn (matchedBlockExtractor n (growingMatchedBlockDepth t) L e x seed) := by
  rw [growingMatchedBlockExtractorRuntime_of_valid t L e _ _ (by simpa using valid)]
  simp only [List.length_ofFn]
  have size := matchedBlockExtractor_growing_seedBits_le n (growingMatchedBlockDepth t) L e
    valid.1 valid.2.1 valid.2.2
  rw [List.take_append_of_le_length (by simpa using size)]
  exact (matchedBlockExtractor_ofFn_take n (growingMatchedBlockDepth t) L e size x seed).symm

end Algebraic.Cutwidth.Extractor.Internal
