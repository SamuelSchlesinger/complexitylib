/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Scheduled.Asymptotics.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Defs
public import Mathlib.Analysis.Asymptotics.Defs
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Scheduled.Asymptotics.Internal

/-!
# A recursive strong extractor with logarithmic seed and sublinear entropy

Fix natural family parameters `a,e`. At input length `n`, take
`L=clog 2 (n+1)`, depth `h=a*clog 2 (L+1)`, and local error exponent
`e+h+2`. The specified recursive map eventually strongly extracts at error
`2^(-e)`, using at most `16384*L` seed bits. Its initial entropy in bits is
little-o of `n`; its output lies between `L^(a+1)` and `2^a*(L+1)^(a+1)`.
The source support threshold is two raised to the entropy-bit threshold.

The finite construction follows the recursive condensation and splitting
method of Chattopadhyay--Goodman--Liao, Theorem 5.6 of *Affine Extractors
for Almost Logarithmic Entropy*, <https://eccc.weizmann.ac.il/report/2021/075/>.
This constant-rate schedule has its own coarser entropy bound. The limit
estimates use Cslib's natural exponential-versus-polynomial theorem and
Mathlib's logarithm and little-o APIs. `Scheduled.Program` gives a uniform
encoded evaluator for the complete variable-depth family
(`scheduledBlockExtractorEval_mem_FP`).
-/

public section

namespace Algebraic.Cutwidth.Extractor

open Filter

/-- For each fixed depth multiplier, the raw depth eventually fits the logarithmic budget. -/
theorem eventually_polylogBlockDepth_le (a : Nat) :
    ∀ᶠ n : Nat in atTop, polylogBlockDepth a n ≤ polylogBlockLength n :=
  Internal.eventually_polylogBlockDepth_le a

/-- The actual initial entropy in bits is sublinear for each fixed family. -/
theorem polylogBlockEntropy_isLittleO (a e : Nat) :
    (fun n => (polylogBlockEntropy a e n : ℝ)) =o[atTop] (fun n => (n : ℝ)) :=
  Internal.polylogBlockEntropy_isLittleO a e

/-- Eventually the required entropy fits within the source's `n` Boolean coordinates. -/
theorem eventually_polylogBlockEntropy_le (a e : Nat) :
    ∀ᶠ n : Nat in atTop, polylogBlockEntropy a e n ≤ n :=
  Internal.eventually_polylogBlockEntropy_le a e

/-- The actual retained seeds eventually occupy at most a fixed multiple of the input logarithm. -/
theorem eventually_polylogBlockSeedBits_le (a e : Nat) :
    ∀ᶠ n : Nat in atTop, polylogBlockSeedBits a e n ≤ 16384 * polylogBlockLength n :=
  Internal.eventually_polylogBlockSeedBits_le a e

/-- The named seed alphabet has exactly the stated binary cardinality, at every input length. -/
theorem card_polylogBlockSeeds (a e n : Nat)
    [∀ s, Fintype (AdjoinRoot (binaryModulus s))] :
    Fintype.card (PolylogBlockSeeds a e n) = 2 ^ polylogBlockSeedBits a e n :=
  Internal.card_polylogBlockSeeds a e n

/-- Finite lower and upper bounds on the number of bits output across all leaves. -/
theorem polylogBlockOutputBits_bounds (a n : Nat) :
    polylogBlockLength n ^ (a + 1) ≤ polylogBlockOutputBits a n ∧
      polylogBlockOutputBits a n ≤ 2 ^ a * (polylogBlockLength n + 1) ^ (a + 1) :=
  Internal.polylogBlockOutputBits_bounds a n

/-- Every fixed family eventually satisfies strong extraction with the actual retained seeds. -/
theorem eventually_polylogBlockExtractor (a e : Nat)
    [∀ s, Fintype (AdjoinRoot (binaryModulus s))] :
    ∀ᶠ n : Nat in atTop,
      WeightedStrongSeededExtractor (polylogBlockExtractor a e n)
        (2 ^ polylogBlockEntropy a e n) (((2 : ℝ) ^ e)⁻¹) :=
  Internal.eventually_polylogBlockExtractor a e

end Algebraic.Cutwidth.Extractor
