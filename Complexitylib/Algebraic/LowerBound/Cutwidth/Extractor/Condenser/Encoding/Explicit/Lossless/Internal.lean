/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Encoding.Explicit.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Lossless.Mixture.Defs
public import Mathlib.Data.Fintype.Pi
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Encoding.Lossless
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Lossless.Mixture
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Parameters.Explicit
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Parameters.Sparse
import Mathlib.Tactic.NormNum

/-!
# Lossless bounds for the explicit runtime schedule

The integer schedule pays for the requested inverse-power-of-two error.
Its proved capacity and field bounds instantiate the decoded runtime
condenser's finite statistical guarantee without additional parameter
inequalities at the use site.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

theorem explicitCondenser_loss (n k e : Nat) {u : Nat} (rate : 0 < u) :
    (((explicitCondenserExtensionDegree n k e u - 1) *
      (2 ^ sparsePowerBits u (explicitCondenserBudget n k e) - 1) *
      condenserCoordinates k (sparsePowerBits u (explicitCondenserBudget n k e)) : Nat) : ℝ) /
        2 ^ sparseFieldBits u (explicitCondenserBudget n k e) ≤ ((2 : ℝ) ^ e)⁻¹ := by
  apply sparseCondenser_loss rate (explicitCondenserBudget_pos n k e)
  rw [mul_comm (((2 : ℝ) ^ e)⁻¹), ← div_eq_mul_inv]
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < 2 ^ e)).mpr
  exact_mod_cast explicitCondenser_error_budget n k e u

theorem decodedExplicitCondenser_flat_lossless (n k e u : Nat)
    [Fintype (AdjoinRoot
      (binaryModulus (sparseFieldExponent u (explicitCondenserBudget n k e))))]
    (rate : 0 < u) (P : Finset (List Bool)) (nonempty : P.Nonempty)
    (source : ∀ bits ∈ P, bits.length = n) (size : P.card ≤ 2 ^ k) :
    let T := explicitCondenserBudget n k e
    let s := sparseFieldExponent u T
    let m := condenserCoordinates k (sparsePowerBits u T)
    ∃ g : AdjoinRoot (binaryModulus s) →
        (P ↪ (Fin m → AdjoinRoot (binaryModulus s))),
      ∀ test : Finset (AdjoinRoot (binaryModulus s) ×
          (Fin m → AdjoinRoot (binaryModulus s))),
        |seededTestProb (fun bits : P => decodedExplicitCondenser n k e u bits.val) test -
          seededTestProb (fun bits y => g y bits) test| ≤ ((2 : ℝ) ^ e)⁻¹ := by
  let T := explicitCondenserBudget n k e
  let s := sparseFieldExponent u T
  let v := explicitCondenserExtensionExponent n k e u
  let r := sparsePowerBits u T
  let m := condenserCoordinates k r
  have entropy : 2 ^ k ≤ (2 ^ r) ^ m := by
    rw [← pow_mul]
    exact Nat.pow_le_pow_right (by decide) (explicitCondenser_entropy_capacity n k e rate)
  have raw := decodedCondenser_flat_lossless s v n
    (List.replicate (3 ^ s) true) (List.replicate (3 ^ v) true)
    (List.replicate r true) (List.replicate m true)
    (by simp) (by simp) (explicitCondenserExtensionExponent_pos n k e u)
    (by simpa only [List.length_replicate, r, s, sparsePowerBits, sparseFieldBits] using
      (Nat.sub_le (sparseFieldBits u T) T))
    (explicitCondenser_source_capacity n k e u) P nonempty source
    (by simpa only [List.length_replicate] using size.trans entropy)
  unfold decodedCondenser at raw
  rw [List.length_replicate, List.length_replicate] at raw
  have close :
      ∃ g : AdjoinRoot (binaryModulus s) →
          (P ↪ (Fin m → AdjoinRoot (binaryModulus s))),
        ∀ test : Finset (AdjoinRoot (binaryModulus s) ×
            (Fin m → AdjoinRoot (binaryModulus s))),
          |seededTestProb (fun bits : P => decodedExplicitCondenser n k e u bits.val) test -
            seededTestProb (fun bits y => g y bits) test| ≤
              (((3 ^ v - 1) * (2 ^ r - 1) * m : Nat) : ℝ) / (2 : ℝ) ^ (2 * 3 ^ s) := by
    unfold decodedExplicitCondenser
    simpa only [explicitCondenserBits,
      sparseFieldBits, explicitCondenserExtensionDegree, List.length_replicate,
      T, s, v, r, m] using raw
  obtain ⟨g, close⟩ := close
  exact ⟨g, fun test => (close test).trans (explicitCondenser_loss n k e rate)⟩

open scoped Classical in
theorem decodedExplicitCondenser_flat_mixture (n k e u : Nat)
    [Fintype (AdjoinRoot
      (binaryModulus (sparseFieldExponent u (explicitCondenserBudget n k e))))]
    (rate : 0 < u) (P : Finset (List Bool))
    (source : ∀ bits ∈ P, bits.length = n) (threshold : 2 ^ k ≤ P.card) :
    let T := explicitCondenserBudget n k e
    let s := sparseFieldExponent u T
    let m := condenserCoordinates k (sparsePowerBits u T)
    ∃ g : ∀ S : P.powersetCard (2 ^ k), AdjoinRoot (binaryModulus s) →
        (S.val ↪ (Fin m → AdjoinRoot (binaryModulus s))),
      ∀ test : Finset (AdjoinRoot (binaryModulus s) ×
          (Fin m → AdjoinRoot (binaryModulus s))),
        |seededTestProb (fun bits : P => decodedExplicitCondenser n k e u bits.val) test -
          seededMixtureTestProb (fun _ : P.powersetCard (2 ^ k) =>
            ((P.powersetCard (2 ^ k)).card : ℝ)⁻¹) (fun S bits y => g S y bits) test| ≤
              ((2 : ℝ) ^ e)⁻¹ := by
  apply exists_flat_mixture_of_exact_size (decodedExplicitCondenser n k e u) P
    (Nat.two_pow_pos k) threshold
  intro S subset card
  exact decodedExplicitCondenser_flat_lossless n k e u rate S
    (Finset.card_pos.mp (card ▸ Nat.two_pow_pos k))
    (fun bits hbits => source bits (subset hbits)) card.le

end Algebraic.Cutwidth.Extractor.Internal
