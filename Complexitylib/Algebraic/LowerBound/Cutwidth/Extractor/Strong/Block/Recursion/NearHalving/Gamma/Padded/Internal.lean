/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.NearHalving.Gamma.Padded.Defs
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.NearHalving.Gamma.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Sampler.Defs
public import Complexitylib.Classes.P.Unary.Defs
public import Mathlib.Order.Filter.AtTopBot.Basic
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.NearHalving.Gamma
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.NearHalving.Gamma.Program
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.NearHalving.Gamma.Program.Family
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.NearHalving.Parameters.Asymptotics
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.NearHalving.Parameters.Unary
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.SeedPadding
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong
import Complexitylib.Tactic.PolyTime
import Mathlib.Data.Fin.Tuple.Take

/-!
# Exact program output and uniform seed padding

The runtime has exactly the requested output length. Its unused seed suffix
does not affect the canonical output, so retaining independent padding
preserves the strong guarantee. All runtime identities cover every word size.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

open Complexity

theorem gammaBlockPaddedExtractor_ofFn (b : Nat) (x : Fin (8 * b) → Bool)
    (seed : Fin (gammaBlockSeedBudget b) → Bool) :
    List.ofFn (gammaBlockPaddedExtractor b x seed) =
      gammaBlockExtractorRuntime b (List.ofFn x) (List.ofFn seed) := by
  apply List.ext_getElem
  · rw [List.length_ofFn, gammaBlockExtractorRuntime_length]
  · intro i hi hbits
    simp only [List.getElem_ofFn, gammaBlockPaddedExtractor,
      List.getElem?_eq_getElem hbits, Option.getD_some]

theorem gammaBlockSeedBits_le_budget {b : Nat} (guard : GammaBlockSizeGuard b) :
    gammaBlockSeedBits b ≤ gammaBlockSeedBudget b :=
  gammaBlockSeedBits_bound guard

theorem gammaBlockPaddedExtractor_eval (b : Nat) (x : Fin (8 * b) → Bool)
    (seed : Fin (gammaBlockSeedBudget b) → Bool) :
    gammaBlockExtractorEval (pair (List.ofFn x) (List.ofFn seed)) =
      List.ofFn (gammaBlockPaddedExtractor b x seed) := by
  rw [gammaBlockExtractorEval_pair, List.length_ofFn,
    Nat.mul_div_cancel_left b (by decide)]
  exact (gammaBlockPaddedExtractor_ofFn b x seed).symm

theorem gammaBlockSeedBudget_unaryFn {b : List Bool → Nat} (hb : UnaryFn b) :
    UnaryFn fun z => gammaBlockSeedBudget (b z) := by
  unfold gammaBlockSeedBudget
  polytime

theorem gammaBlockPaddedExtractor_eq (b : Nat) (guard : GammaBlockSizeGuard b)
    (x : Fin (8 * b) → Bool) (seed : Fin (gammaBlockSeedBudget b) → Bool) :
    gammaBlockPaddedExtractor b x seed = gammaBlockExtractor b x
      (fun j => seed (Fin.castLE (gammaBlockSeedBits_le_budget guard) j)) := by
  have reconstruction :
      List.ofFn (fun j => seed (Fin.castLE (gammaBlockSeedBits_le_budget guard) j)) ++
        (List.ofFn seed).drop (gammaBlockSeedBits b) = List.ofFn seed := by
    change List.ofFn (Fin.take (gammaBlockSeedBits b) (gammaBlockSeedBits_le_budget guard) seed) ++
      (List.ofFn seed).drop (gammaBlockSeedBits b) = List.ofFn seed
    rw [Fin.ofFn_take_eq_take_ofFn]
    exact List.take_append_drop _ _
  have correct := gammaBlockExtractorRuntime_append_eq b guard x
    (fun j => seed (Fin.castLE (gammaBlockSeedBits_le_budget guard) j))
    ((List.ofFn seed).drop (gammaBlockSeedBits b))
  rw [reconstruction] at correct
  apply List.ofFn_injective
  rw [gammaBlockPaddedExtractor_ofFn, correct]

theorem gammaBlockPaddedExtractor_weighted {b : Nat} (guard : GammaBlockSizeGuard b) :
    WeightedStrongSeededExtractor (gammaBlockPaddedExtractor b) (2 ^ (2 * b)) (1 / 4) := by
  have correct : gammaBlockPaddedExtractor b = fun x seed => gammaBlockExtractor b x
      (fun j => seed (Fin.castLE (gammaBlockSeedBits_le_budget guard) j)) := by
    funext x seed
    exact gammaBlockPaddedExtractor_eq b guard x seed
  rw [correct]
  exact (gammaBlockExtractor_weighted guard).padSeed (gammaBlockSeedBits_le_budget guard)

theorem gammaBlockPaddedExtractor_flat {b : Nat} (guard : GammaBlockSizeGuard b) :
    FlatSeededExtractor (gammaBlockPaddedExtractor b) (2 ^ (2 * b)) (1 / 4) :=
  (gammaBlockPaddedExtractor_weighted guard).flatStrongSeededExtractor.flatSeededExtractor

theorem eventually_gammaBlockPaddedExtractor_weighted :
    ∀ᶠ b : Nat in Filter.atTop,
      WeightedStrongSeededExtractor (gammaBlockPaddedExtractor b) (2 ^ (2 * b)) (1 / 4) :=
  eventually_gammaBlockSizeGuard.mono fun _ guard => gammaBlockPaddedExtractor_weighted guard

theorem eventually_gammaBlockPaddedExtractor_flat :
    ∀ᶠ b : Nat in Filter.atTop,
      FlatSeededExtractor (gammaBlockPaddedExtractor b) (2 ^ (2 * b)) (1 / 4) :=
  eventually_gammaBlockSizeGuard.mono fun _ guard => gammaBlockPaddedExtractor_flat guard

end Algebraic.Cutwidth.Extractor.Internal
