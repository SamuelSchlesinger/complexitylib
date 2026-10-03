/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Encoding.Explicit.Defs
public import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Two equal bit-vector outputs from the scheduled condenser

Every selected field element has width `2 * 3^s`, so the complete coordinate
output has even length. Split that actual output word into two consecutive
halves, without adding padding or dropping any coordinate bits.

The semantic field seed is encoded by the existing quotient codec before
calling the runtime condenser. These definitions add no new randomness or
parameter promise; their statistical guarantees require a positive rate.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Extractor

/-- Half the scheduled condenser's exact bit-output length. -/
def explicitCondenserHalfWidth (n k e u : Nat) : Nat :=
  condenserCoordinates k (sparsePowerBits u (explicitCondenserBudget n k e)) *
    3 ^ sparseFieldExponent u (explicitCondenserBudget n k e)

/-- Read the first and second halves of the actual scheduled output at a canonical field seed. -/
noncomputable def explicitCondenserPair (n k e u : Nat) (x : Fin n → Bool)
    (seed : AdjoinRoot (binaryModulus
      (sparseFieldExponent u (explicitCondenserBudget n k e)))) :
    (Fin (explicitCondenserHalfWidth n k e u) → Bool) ×
      (Fin (explicitCondenserHalfWidth n k e u) → Bool) :=
  let half := explicitCondenserHalfWidth n k e u
  let bits := explicitCondenserBits n k e u (List.ofFn x)
    (BinaryFieldCodec.encode (sparseFieldExponent u (explicitCondenserBudget n k e)) seed)
  (Fin.appendEquiv half half).symm (fun i => bits[i.val]?.getD false)

end Algebraic.Cutwidth.Extractor
