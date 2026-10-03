/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.OneShot.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Defs
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Encoding.Serialization.Defs
public import Mathlib.Data.Fintype.Pi
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.OneShot.Extraction.Internal.Hashing
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.OneShot.Parameters
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Composition
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Hashing
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Encoding.Explicit.Lossless
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.Positivity

/-!
# The one-shot statistical composition

The actual selected condenser is close to a uniform mixture of conditional
flat sources of size `2^(ell+2*e)`. Exact serialization and a universal
binary field hash extract from each such source with error `2^(-(e+1))`.
The retained-seed composition theorem adds this to the condenser's same
half-error. Both independent seeds remain visible in every final test.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

open scoped Classical

theorem oneShot_composition_flat (n ell e : Nat)
    [condenserFinite : Fintype
      (AdjoinRoot (binaryModulus (oneShotCondenserExponent n ell e)))]
    [Fintype (AdjoinRoot (binaryModulus (oneShotHashExponent n ell e)))]
    (P : Finset (List Bool)) (source : ∀ bits ∈ P, bits.length = n)
    (threshold : 2 ^ (ell + 2 * e) ≤ P.card) :
    let m := condenserCoordinates (ell + 2 * e)
      (sparsePowerBits 1 (explicitCondenserBudget n (ell + 2 * e) (e + 1)))
    ∀ test : Finset ((AdjoinRoot (binaryModulus (oneShotCondenserExponent n ell e)) ×
        AdjoinRoot (binaryModulus (oneShotHashExponent n ell e))) × (Fin ell → ZMod 2)),
      |seededTestProb (fun bits : P => fun seeds =>
          binaryFieldHash (oneShotHashExponent n ell e) ell
            (BinaryFieldCodec.decode (oneShotHashExponent n ell e)
              (encodeCondenserOutput (oneShotCondenserExponent n ell e) m
                (decodedExplicitCondenser n (ell + 2 * e) (e + 1) 1 bits.val seeds.1)))
            seeds.2) test - uniformSeededTestProb test| ≤ ((2 : ℝ) ^ e)⁻¹ := by
  dsimp only
  let : Fintype (AdjoinRoot (binaryModulus
      (sparseFieldExponent 1 (explicitCondenserBudget n (ell + 2 * e) (e + 1))))) :=
    condenserFinite
  let m := condenserCoordinates (ell + 2 * e)
    (sparsePowerBits 1 (explicitCondenserBudget n (ell + 2 * e) (e + 1)))
  let H (coords : Fin m → AdjoinRoot (binaryModulus (oneShotCondenserExponent n ell e))) :=
    binaryFieldHash (oneShotHashExponent n ell e) ell
      (BinaryFieldCodec.decode (oneShotHashExponent n ell e)
        (encodeCondenserOutput (oneShotCondenserExponent n ell e) m coords))
  have capacity : m * (2 * 3 ^ oneShotCondenserExponent n ell e) ≤
      2 * 3 ^ oneShotHashExponent n ell e := by
    simpa only [oneShotCondenserOutputBits, oneShotCondenserExponent, sparseFieldBits, m] using
      oneShotHashBits_source_capacity n ell e
  have universal : UniversalHashFamily H :=
    serializedBinaryHash_universal capacity (oneShotHashBits_output_capacity n ell e)
  have positive : 0 < 2 ^ (ell + 2 * e) := by positivity
  have extract : FlatStrongSeededExtractor H (2 ^ (ell + 2 * e))
      (((2 : ℝ) ^ (e + 1))⁻¹) := by
    apply universal.flatStrongSeededExtractor positive (by positivity)
    simpa only [Fintype.card_fun, Fintype.card_fin, ZMod.card, Nat.cast_pow,
      Nat.cast_ofNat] using oneShot_leftover_budget ell e
  obtain ⟨g, close⟩ :=
    decodedExplicitCondenser_flat_mixture n (ell + 2 * e) (e + 1) 1
      (by decide) P source threshold
  have subset_pos : 0 < (P.powersetCard (2 ^ (ell + 2 * e))).card := by
    simpa only [Finset.card_powersetCard] using Nat.choose_pos threshold
  have mass : (∑ _ : P.powersetCard (2 ^ (ell + 2 * e)),
      ((P.powersetCard (2 ^ (ell + 2 * e))).card : ℝ)⁻¹) = 1 := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]
    exact mul_inv_cancel₀ (by positivity)
  intro test
  have bound := seededTestProb_comp_of_flat_mixture
    (fun bits : P => decodedExplicitCondenser n (ell + 2 * e) (e + 1) 1 bits.val) H
    (fun _ : P.powersetCard (2 ^ (ell + 2 * e)) =>
      ((P.powersetCard (2 ^ (ell + 2 * e))).card : ℝ)⁻¹) g
    (fun _ => by positivity) mass positive (fun S => by
      rw [Fintype.card_coe, (Finset.mem_powersetCard.mp S.property).2]) extract close test
  rw [oneShot_half_errors] at bound
  convert bound using 1
  dsimp only [H, m]
  congr 2

end Algebraic.Cutwidth.Extractor.Internal
