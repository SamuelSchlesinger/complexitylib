/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.SourceReduction.Sampler.Program.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.SourceReduction.Sampler.Defs
public import Complexitylib.Classes.P.Defs
public import Complexitylib.Classes.P.Unary.Defs
public import Complexitylib.Tactic.PolyTime.Init
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.SourceReduction.Sampler.Program.Internal

/-!
# A uniform total evaluator for the amplified sampler

Both component algorithms run on actual input words. The evaluator returns
exactly the requested output width on every input, with false completion
when necessary. Canonical inputs agree with the Boolean sampler under the
growing-extractor guard; no Gamma size guard is needed for that identity.
The FP certificates are unconditional and accept computed unary widths.
They concern one sampled position, not enumeration of an entire parameter
family's outer words and candidates.
-/

public section

namespace Algebraic.Cutwidth.Extractor

/-- Every input, including invalid component parameters, produces exactly `d` bits. -/
theorem amplifiedMatchedSamplerRuntime_length (L d : Nat) (source outer candidate : List Bool) :
    (amplifiedMatchedSamplerRuntime L d source outer candidate).length = d :=
  Internal.amplifiedMatchedSamplerRuntime_length L d source outer candidate

/-- The actual word program computes the canonical Boolean sampler under its growing guard. -/
theorem amplifiedMatchedSamplerRuntime_eq_amplifiedMatchedSampler (n L d : Nat)
    (base : GrowingMatchedBlockRuntimeValid n d L 4) (x : Fin n → Bool)
    (outer : Fin (8 * matchedBlockSeedBits L) → Bool)
    (candidate : Fin (gammaBlockSeedBudget (matchedBlockSeedBits L)) → Bool) :
    amplifiedMatchedSamplerRuntime L d (List.ofFn x) (List.ofFn outer) (List.ofFn candidate) =
      List.ofFn (amplifiedMatchedSampler n L d x outer candidate) :=
  Internal.amplifiedMatchedSamplerRuntime_eq_amplifiedMatchedSampler n L d base x outer candidate

open Complexity in
/-- Computed unary widths and three runtime words give one polynomial-time composition. -/
@[polytime] theorem amplifiedMatchedSamplerRuntime_mem_FP {L d : List Bool → Nat}
    {source outer candidate : List Bool → List Bool} (hL : UnaryFn L) (hd : UnaryFn d)
    (hsource : source ∈ FP) (houter : outer ∈ FP) (hcandidate : candidate ∈ FP) :
    (fun z => amplifiedMatchedSamplerRuntime (L z) (d z)
      (source z) (outer z) (candidate z)) ∈ FP :=
  Internal.amplifiedMatchedSamplerRuntime_mem_FP hL hd hsource houter hcandidate

open Complexity in
/-- Decoding the paired input passes all words and unary lengths to the actual runtime. -/
theorem amplifiedMatchedSamplerEval_pair (source outer candidate scale outputWidth : List Bool) :
    amplifiedMatchedSamplerEval
      (pair (pair source (pair outer candidate)) (pair scale outputWidth)) =
      amplifiedMatchedSamplerRuntime scale.length outputWidth.length source outer candidate :=
  Internal.amplifiedMatchedSamplerEval_pair source outer candidate scale outputWidth

open Complexity in
/-- The decoded output-width word determines the output length on every encoded input. -/
theorem amplifiedMatchedSamplerEval_length (z : List Bool) :
    (amplifiedMatchedSamplerEval z).length = (pairSnd (pairSnd z)).length :=
  Internal.amplifiedMatchedSamplerEval_length z

/-- The paired evaluator's output never exceeds its encoded input length. -/
theorem amplifiedMatchedSamplerEval_length_le (z : List Bool) :
    (amplifiedMatchedSamplerEval z).length ≤ z.length :=
  Internal.amplifiedMatchedSamplerEval_length_le z

open Complexity in
/-- A single total polynomial-time evaluator computes the sampler on every paired word. -/
@[polytime] theorem amplifiedMatchedSamplerEval_mem_FP : amplifiedMatchedSamplerEval ∈ FP :=
  Internal.amplifiedMatchedSamplerEval_mem_FP

end Algebraic.Cutwidth.Extractor
