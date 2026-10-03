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
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Encoding.Explicit.Lossless.Internal

/-!
# Lossless condensation with explicitly selected runtime parameters

The schedule chooses the field, extension degree, powering stride, and
coordinate count from source length `n`, entropy budget `k`, inverse-error
exponent `e`, and positive rate parameter `u`. The resulting runtime map
has retained-seed test error at most `2^(-e)` on every qualifying flat source.
All algebraic and numerical capacity conditions follow from this schedule.

At support sizes at most `2^k`, each ideal seed fiber is uniform on as many
outputs as there are source points. Larger supports admit an explicit
mixture of conditional `2^k`-flat witnesses with the same error. These finite
statistical consequences combine the checked GUV expansion proof with the
explicit sparse parameter choice and runtime correctness. Asymptotic bounds
and the higher extractor composition are separate results.
-/

public section

namespace Algebraic.Cutwidth.Extractor

/-- The selected extension and slack budget pay for inverse-power-of-two error. -/
theorem explicitCondenser_loss (n k e : Nat) {u : Nat} (rate : 0 < u) :
    (((explicitCondenserExtensionDegree n k e u - 1) *
      (2 ^ sparsePowerBits u (explicitCondenserBudget n k e) - 1) *
      condenserCoordinates k (sparsePowerBits u (explicitCondenserBudget n k e)) : Nat) : ℝ) /
        2 ^ sparseFieldBits u (explicitCondenserBudget n k e) ≤ ((2 : ℝ) ^ e)⁻¹ :=
  Internal.explicitCondenser_loss n k e rate

/-- Every nonempty flat `n`-bit source of size at most `2^k` has a seedwise flat
witness within the requested error. All parameters are selected before `P`. -/
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
          seededTestProb (fun bits y => g y bits) test| ≤ ((2 : ℝ) ^ e)⁻¹ :=
  Internal.decodedExplicitCondenser_flat_lossless n k e u rate P nonempty source size

open scoped Classical in
/-- Every flat `n`-bit support of size at least `2^k` is close to an explicit
mixture of conditional `2^k`-flat outputs, retaining the uniform seed. -/
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
              ((2 : ℝ) ^ e)⁻¹ :=
  Internal.decodedExplicitCondenser_flat_mixture n k e u rate P source threshold

end Algebraic.Cutwidth.Extractor
