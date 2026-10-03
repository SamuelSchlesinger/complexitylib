/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Encoding.Explicit.Pair.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Condenser.Defs
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Encoding.Explicit.Pair.Internal

/-!
# The scheduled condenser with two equal Boolean-vector outputs

Splitting the actual serialized output into two consecutive halves preserves
its length, entropy threshold, and statistical error. The field bit width is
even, so no padding or rounding loss is needed. Each half has alphabet size
`2^H`, where `H = explicitCondenserHalfWidth n k e u`, including `H = 0`.

This represents the existing scheduled condenser in the pair-output form
used by block splitting. The underlying algebraic map and parameter source
credits remain in `Condenser.Polynomial` and `Parameters.Sparse`. No recursive
parameter schedule or polynomial-time certificate for a block loop is asserted.
-/

public section

namespace Algebraic.Cutwidth.Extractor

/-- Two halves cover the exact coordinate output width, without padding. -/
theorem explicitCondenserHalfWidth_double (n k e u : Nat) :
    explicitCondenserHalfWidth n k e u + explicitCondenserHalfWidth n k e u =
      condenserCoordinates k (sparsePowerBits u (explicitCondenserBudget n k e)) *
        sparseFieldBits u (explicitCondenserBudget n k e) :=
  Internal.explicitCondenserHalfWidth_double n k e u

/-- Representing the output as two halves retains the original exact rate bound. -/
theorem explicitCondenserHalfWidth_rate (n k e u : Nat) :
    u * (explicitCondenserHalfWidth n k e u + explicitCondenserHalfWidth n k e u) ≤
      (u + 1) * k + u * sparseFieldBits u (explicitCondenserBudget n k e) :=
  Internal.explicitCondenserHalfWidth_rate n k e u

/-- The first half reads the beginning of the actual program output. -/
theorem explicitCondenserPair_fst (n k e u : Nat) (x : Fin n → Bool)
    (seed : AdjoinRoot (binaryModulus
      (sparseFieldExponent u (explicitCondenserBudget n k e))))
    (i : Fin (explicitCondenserHalfWidth n k e u)) :
    (explicitCondenserPair n k e u x seed).1 i =
      (explicitCondenserBits n k e u (List.ofFn x)
        (BinaryFieldCodec.encode (sparseFieldExponent u (explicitCondenserBudget n k e))
          seed))[i.val]?.getD false := rfl

/-- The second half immediately follows the first in the actual program output. -/
theorem explicitCondenserPair_snd (n k e u : Nat) (x : Fin n → Bool)
    (seed : AdjoinRoot (binaryModulus
      (sparseFieldExponent u (explicitCondenserBudget n k e))))
    (i : Fin (explicitCondenserHalfWidth n k e u)) :
    (explicitCondenserPair n k e u x seed).2 i =
      (explicitCondenserBits n k e u (List.ofFn x)
        (BinaryFieldCodec.encode (sparseFieldExponent u (explicitCondenserBudget n k e))
          seed))[explicitCondenserHalfWidth n k e u + i.val]?.getD false := rfl

/-- The actual paired output strongly condenses every capped input source
with the same entropy threshold and error as its field-coordinate representation. -/
theorem explicitCondenserPair_weighted (n k e u : Nat)
    [Fintype (AdjoinRoot
      (binaryModulus (sparseFieldExponent u (explicitCondenserBudget n k e))))]
    (rate : 0 < u) :
    WeightedStrongSeededCondenser (explicitCondenserPair n k e u) (2 ^ k) (2 ^ k)
      ((2 : ℝ) ^ e)⁻¹ :=
  Internal.explicitCondenserPair_weighted n k e u rate

end Algebraic.Cutwidth.Extractor
