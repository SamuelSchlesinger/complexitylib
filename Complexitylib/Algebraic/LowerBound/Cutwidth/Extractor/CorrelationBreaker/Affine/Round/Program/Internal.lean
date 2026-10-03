/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.Round.Program.Defs
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.Round.Defs
public import Complexitylib.Classes.P.Defs
public import Complexitylib.Classes.P.Unary.Defs
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Scheduled.Matched.Program
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Scheduled.Matched.Growing.Program
import Complexitylib.Tactic.PolyTime
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Correctness, guard arithmetic, and uniform computation of one affine round

The prefix identity covers false completion even below the short seed
width. Canonical correctness then follows through all four component calls.
Every component's total FP certificate applies before any validity premise
is used; the growing depth has polynomially many leaves in the unary count.
Its final output bounds the entire encoded evaluator's output length.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

open Complexity

theorem affineRoundPrefixWord_length (L : Nat) (row : List Bool) :
    (affineRoundPrefixWord L row).length = matchedBlockSeedBits L := by
  simp only [affineRoundPrefixWord, List.length_take, List.length_append, List.length_replicate]
  exact min_eq_left (by lia)

theorem affineRoundPrefix_ofFn (h L : Nat) (row : Fin (matchedBlockOutputBits h L) → Bool) :
    List.ofFn (affineRoundPrefix h L row) = affineRoundPrefixWord L (List.ofFn row) := by
  apply List.ext_getElem
  · rw [List.length_ofFn, affineRoundPrefixWord_length]
  · intro i hi hj
    simp only [List.getElem_ofFn, affineRoundPrefix, affineRoundPrefixWord, List.getElem_take]
    by_cases inside : i < (List.ofFn row).length
    · rw [List.getElem?_eq_getElem inside, Option.getD_some, List.getElem_append_left inside]
    · rw [List.getElem?_eq_none (by lia), Option.getD_none,
        List.getElem_append_right (by lia), List.getElem_replicate]

theorem affineRoundRuntime_short_guard (n d t L e : Nat)
    (growing : GrowingMatchedBlockRuntimeValid n t L e) (length : Nat.clog 2 (d + 1) ≤ L) :
    MatchedBlockRuntimeValid d 24 L e := by
  have depth : 64 ≤ growingMatchedBlockDepth t := Nat.le_add_left _ _
  have error := growing.2.1
  exact ⟨by lia, by decide, by lia, length⟩

theorem affineRoundRuntime_row_guard (n t L e : Nat)
    (growing : GrowingMatchedBlockRuntimeValid n t L e) :
    MatchedBlockRuntimeValid (matchedBlockOutputBits (growingMatchedBlockDepth t) L) 24 L e := by
  apply affineRoundRuntime_short_guard n _ t L e growing
  let h := growingMatchedBlockDepth t
  have power : matchedBlockOutputBits h L + 1 ≤ 2 ^ (h + Nat.clog 2 (L + 1)) := by
    calc
      _ ≤ 2 ^ h * (L + 1) := by
        unfold matchedBlockOutputBits
        rw [Nat.mul_add, Nat.mul_one]
        have positive : 0 < (2 : Nat) ^ h := by positivity
        lia
      _ ≤ 2 ^ h * 2 ^ Nat.clog 2 (L + 1) :=
        Nat.mul_le_mul_left _ (Nat.le_pow_clog (by decide) (L + 1))
      _ = _ := (pow_add 2 h (Nat.clog 2 (L + 1))).symm
  apply (Nat.clog_le_of_le_pow power).trans
  have factor : e + 2 * h + Nat.clog 2 (L + 1) + 4 ≤
      (h + 1) * (e + 2 * h + Nat.clog 2 (L + 1) + 4) :=
    Nat.le_mul_of_pos_left _ (Nat.succ_pos h)
  have inside : h + Nat.clog 2 (L + 1) ≤ e + 2 * h + Nat.clog 2 (L + 1) + 4 := by lia
  exact inside.trans (factor.trans growing.2.2)

theorem affineRoundRuntime_eq_affineRoundOutput (n d t L e : Nat)
    (right : MatchedBlockRuntimeValid d 24 L e)
    (rowGuard : MatchedBlockRuntimeValid
      (matchedBlockOutputBits (growingMatchedBlockDepth t) L) 24 L e)
    (last : GrowingMatchedBlockRuntimeValid n t L e)
    (x : Fin n → Bool) (y : Fin d → Bool)
    (row : Fin (matchedBlockOutputBits (growingMatchedBlockDepth t) L) → Bool) :
    affineRoundRuntime t L e (List.ofFn x) (List.ofFn y) (List.ofFn row) =
      List.ofFn (affineRoundOutput n d (growingMatchedBlockDepth t) L e x y row) := by
  let h := growingMatchedBlockDepth t
  have first : matchedBlockExtractorRuntime 24 L e (List.ofFn y)
      (affineRoundPrefixWord L (List.ofFn row)) =
      List.ofFn (affineRoundMiddleSeed d h L e y row) := by
    rw [← affineRoundPrefix_ofFn]
    exact matchedBlockExtractorRuntime_eq_matchedBlockExtractor d 24 L e right y _
  have second := (congrArg (matchedBlockExtractorRuntime 24 L e (List.ofFn row)) first).trans
    (matchedBlockExtractorRuntime_eq_matchedBlockExtractor _ 24 L e rowGuard row
      (affineRoundMiddleSeed d h L e y row))
  have third := (congrArg (matchedBlockExtractorRuntime 24 L e (List.ofFn y)) second).trans
    (matchedBlockExtractorRuntime_eq_matchedBlockExtractor d 24 L e right y
      (affineRoundMiddleOutput d h L e y row))
  have fourth := (congrArg (growingMatchedBlockExtractorRuntime t L e (List.ofFn x)) third).trans
    (growingMatchedBlockExtractorRuntime_eq_matchedBlockExtractor n t L e last x
      (affineRoundFinalSeed d h L e y row))
  exact fourth

theorem affineRoundRuntime_short_length_le (L e : Nat) (source seeds : List Bool) :
    (matchedBlockExtractorRuntime 24 L e source seeds).length ≤ matchedBlockSeedBits L := by
  rw [matchedBlockExtractorRuntime_length]
  split_ifs
  · exact le_rfl
  · exact Nat.zero_le _

theorem affineRoundRuntime_length (t L e : Nat) (x y row : List Bool) :
    (affineRoundRuntime t L e x y row).length =
      if GrowingMatchedBlockRuntimeValid x.length t L e then
        2 ^ growingMatchedBlockDepth t * L else 0 :=
  growingMatchedBlockExtractorRuntime_length _ _ _ _ _

theorem affineRoundRuntime_length_le (t L e : Nat) (x y row : List Bool) :
    (affineRoundRuntime t L e x y row).length ≤ 2 ^ 65 * (t + 1) * L :=
  growingMatchedBlockExtractorRuntime_length_le _ _ _ _ _

theorem affineRoundPrefixWord_mem_FP {L : List Bool → Nat} {row : List Bool → List Bool}
    (hL : UnaryFn L) (hrow : row ∈ FP) : (fun z => affineRoundPrefixWord (L z) (row z)) ∈ FP := by
  polytime [affineRoundPrefixWord, matchedBlockSeedBits]

theorem affineRoundRuntime_mem_FP {t L e : List Bool → Nat} {x y row : List Bool → List Bool}
    (ht : UnaryFn t) (hL : UnaryFn L) (he : UnaryFn e)
    (hx : x ∈ FP) (hy : y ∈ FP) (hrow : row ∈ FP) :
    (fun z => affineRoundRuntime (t z) (L z) (e z) (x z) (y z) (row z)) ∈ FP := by
  have prefixProgram := affineRoundPrefixWord_mem_FP hL hrow
  polytime [affineRoundRuntime]

theorem affineRoundEval_pair (x y row parameter scale error : List Bool) :
    affineRoundEval (pair (pair x (pair y row)) (pair parameter (pair scale error))) =
      affineRoundRuntime parameter.length scale.length error.length x y row := by
  simp only [affineRoundEval, pairFst_pair, pairSnd_pair]

theorem affineRoundEval_mem_FP : affineRoundEval ∈ FP := by
  unfold affineRoundEval
  apply affineRoundRuntime_mem_FP <;> polytime

theorem affineRoundEval_length_le (z : List Bool) :
    (affineRoundEval z).length ≤ 2 ^ 65 * (z.length + 1) ^ 2 := by
  have parameter := (pairFst_length_le (pairSnd z)).trans (pairSnd_length_le z)
  have scale := (pairFst_length_le (pairSnd (pairSnd z))).trans
    ((pairSnd_length_le (pairSnd z)).trans (pairSnd_length_le z))
  calc
    (affineRoundEval z).length ≤
        2 ^ 65 * ((pairFst (pairSnd z)).length + 1) *
          (pairFst (pairSnd (pairSnd z))).length := affineRoundRuntime_length_le _ _ _ _ _ _
    _ ≤ 2 ^ 65 * (z.length + 1) * (z.length + 1) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ (Nat.add_le_add_right parameter 1))
        (scale.trans (Nat.le_succ _))
    _ = 2 ^ 65 * (z.length + 1) ^ 2 := by ring

end Algebraic.Cutwidth.Extractor.Internal
