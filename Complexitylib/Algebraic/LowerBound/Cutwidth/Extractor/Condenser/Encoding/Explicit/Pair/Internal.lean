/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Encoding.Explicit.Pair.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Condenser.Defs
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Encoding.Explicit
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Encoding.Explicit.Weighted
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Encoding.Serialization
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Condenser.Transport
import Mathlib.Tactic.Ring

/-!
# Serialization and statistical transport for the scheduled pair output

Reading two halves is injective on words of the prescribed length.
Serialization is independently injective on field-coordinate vectors,
and re-encoding the decoded runtime output gives its actual bits.
Transporting the scheduled condenser through these two injections therefore
preserves its conditional cap and joint statistical error.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

private def wordPair (h : Nat) (bits : List Bool) : (Fin h → Bool) × (Fin h → Bool) :=
  (Fin.appendEquiv h h).symm (fun i => bits[i.val]?.getD false)

private theorem wordPair_injective_of_length {h n : Nat} {a b : List Bool}
    (ha : a.length = n) (hb : b.length = n) (capacity : n ≤ h + h)
    (same : wordPair h a = wordPair h b) : a = b := by
  have allBits := (Fin.appendEquiv h h).symm.injective same
  apply List.ext_getElem (ha.trans hb.symm)
  intro i hi hj
  have bound : i < h + h := lt_of_lt_of_le (ha ▸ hi) capacity
  have sameBit := congrFun allBits ⟨i, bound⟩
  simpa [List.getElem?_eq_getElem, hi, hj] using sameBit

private noncomputable def coordinatePair (s c h : Nat)
    (coords : Fin c → AdjoinRoot (binaryModulus s)) :
    (Fin h → Bool) × (Fin h → Bool) :=
  wordPair h (encodeCondenserOutput s c coords)

private theorem coordinatePair_injective (s c h : Nat)
    (capacity : c * (2 * 3 ^ s) ≤ h + h) : Function.Injective (coordinatePair s c h) := by
  intro a b same
  apply encodeCondenserOutput_injective s c
  exact wordPair_injective_of_length (encodeCondenserOutput_length s c a)
    (encodeCondenserOutput_length s c b) capacity same

theorem explicitCondenserHalfWidth_double (n k e u : Nat) :
    explicitCondenserHalfWidth n k e u + explicitCondenserHalfWidth n k e u =
      condenserCoordinates k (sparsePowerBits u (explicitCondenserBudget n k e)) *
        sparseFieldBits u (explicitCondenserBudget n k e) := by
  unfold explicitCondenserHalfWidth sparseFieldBits
  ring

theorem explicitCondenserHalfWidth_rate (n k e u : Nat) :
    u * (explicitCondenserHalfWidth n k e u + explicitCondenserHalfWidth n k e u) ≤
      (u + 1) * k + u * sparseFieldBits u (explicitCondenserBudget n k e) := by
  rw [explicitCondenserHalfWidth_double]
  simpa only [explicitCondenserBits_length] using
    explicitCondenserBits_output_rate n k e u [] []

private theorem encode_decoded_explicit (n k e u : Nat) (bits : List Bool)
    (seed : AdjoinRoot (binaryModulus
      (sparseFieldExponent u (explicitCondenserBudget n k e)))) :
    encodeCondenserOutput (sparseFieldExponent u (explicitCondenserBudget n k e))
        (condenserCoordinates k (sparsePowerBits u (explicitCondenserBudget n k e)))
        (decodedExplicitCondenser n k e u bits seed) =
      explicitCondenserBits n k e u bits
        (BinaryFieldCodec.encode (sparseFieldExponent u (explicitCondenserBudget n k e)) seed) := by
  apply encode_decodeCondenserOutput
  exact explicitCondenserBits_length n k e u bits _

private theorem explicitCondenserPair_eq_coordinates (n k e u : Nat) (x : Fin n → Bool)
    (seed : AdjoinRoot (binaryModulus
      (sparseFieldExponent u (explicitCondenserBudget n k e)))) :
    explicitCondenserPair n k e u x seed =
      coordinatePair (sparseFieldExponent u (explicitCondenserBudget n k e))
        (condenserCoordinates k (sparsePowerBits u (explicitCondenserBudget n k e)))
        (explicitCondenserHalfWidth n k e u)
        (decodedExplicitCondenser n k e u (List.ofFn x) seed) := by
  unfold explicitCondenserPair coordinatePair wordPair
  rw [encode_decoded_explicit]

theorem explicitCondenserPair_weighted (n k e u : Nat)
    [Fintype (AdjoinRoot
      (binaryModulus (sparseFieldExponent u (explicitCondenserBudget n k e))))]
    (rate : 0 < u) :
    WeightedStrongSeededCondenser (explicitCondenserPair n k e u) (2 ^ k) (2 ^ k)
      ((2 : ℝ) ^ e)⁻¹ := by
  have result :=
    (decodedExplicitCondenser_weighted_ofFn n k e u rate).map_output_injective
      (fun _ => coordinatePair (sparseFieldExponent u (explicitCondenserBudget n k e))
        (condenserCoordinates k (sparsePowerBits u (explicitCondenserBudget n k e)))
        (explicitCondenserHalfWidth n k e u))
      (fun _ => coordinatePair_injective _ _ _ (by
        rw [explicitCondenserHalfWidth_double]
        rfl))
  simpa only [← explicitCondenserPair_eq_coordinates] using result

end Algebraic.Cutwidth.Extractor.Internal
