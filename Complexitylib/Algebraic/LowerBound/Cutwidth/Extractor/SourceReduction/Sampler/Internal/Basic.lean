/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.SourceReduction.Sampler.Defs
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Scheduled.Matched
import Mathlib.Tactic.Linarith

/-!
# Output capacity and source linearity of the amplified sampler

Logarithmic depth already gives at least the requested output width at
every positive scale. Source XOR is preserved even when a total prefix
uses false completion.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

theorem amplifiedMatchedSampler_output_capacity (L d : Nat) (positive : 0 < L) :
    d ≤ matchedBlockOutputBits (growingMatchedBlockDepth d) L := by
  calc
    d ≤ d + 1 := Nat.le_succ d
    _ ≤ 2 ^ Nat.clog 2 (d + 1) := Nat.le_pow_clog (by decide) _
    _ ≤ 2 ^ growingMatchedBlockDepth d :=
      Nat.pow_le_pow_right (by decide) (Nat.le_add_right _ _)
    _ ≤ 2 ^ growingMatchedBlockDepth d * L := Nat.le_mul_of_pos_right _ positive

theorem amplifiedMatchedSampler_eq_prefix (n L d : Nat) (positive : 0 < L)
    (x : Fin n → Bool) (outer : Fin (8 * matchedBlockSeedBits L) → Bool)
    (candidate : Fin (gammaBlockSeedBudget (matchedBlockSeedBits L)) → Bool) :
    amplifiedMatchedSampler n L d x outer candidate = fun j =>
      matchedBlockExtractor n (growingMatchedBlockDepth d) L 4 x
        (gammaBlockPaddedExtractor (matchedBlockSeedBits L) outer candidate)
        (Fin.castLE (amplifiedMatchedSampler_output_capacity L d positive) j) := by
  funext j
  have inside := j.isLt.trans_le (amplifiedMatchedSampler_output_capacity L d positive)
  simp only [amplifiedMatchedSampler, List.getElem?_ofFn, inside, dite_eq_left, Option.getD_some]
  rfl

theorem amplifiedMatchedSampler_xor (n L d : Nat) (x x' : Fin n → Bool)
    (outer : Fin (8 * matchedBlockSeedBits L) → Bool)
    (candidate : Fin (gammaBlockSeedBudget (matchedBlockSeedBits L)) → Bool) :
    amplifiedMatchedSampler n L d (fun i => Bool.xor (x i) (x' i)) outer candidate =
      fun j => Bool.xor (amplifiedMatchedSampler n L d x outer candidate j)
        (amplifiedMatchedSampler n L d x' outer candidate j) := by
  funext j
  simp only [amplifiedMatchedSampler, matchedBlockExtractor_xor, List.getElem?_ofFn]
  split_ifs <;> simp

end Algebraic.Cutwidth.Extractor.Internal
