/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.SourceReduction.Leakage.Defs
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.SourceReduction.Leakage.Parity.Internal

/-!
# Parity bounds for the actual leaked affine outputs

A balanced bit of the honest output has small sign expectation after XOR
with any function of all retained tampered outputs. The more general real
mask theorem permits any tag statistic of absolute value at most one,
including a product of tampered signs. The sign convention is `true ↦ 1`
and `false ↦ -1`.

These are finite weighted consequences of the conditional-uniformity
comparison used in Chattopadhyay--Liao, *Extractors for Sum of Two Sources*,
Lemmas 5.3--5.4: <https://arxiv.org/abs/2110.12652>. The calculation is valid
for raw signed weights, so normalization is unnecessary. The actual-law
corollaries require membership outside the defined bad-seed set; they do
not assume a parity guarantee or a new correlation breaker.
-/

public section

namespace Algebraic.Cutwidth.Extractor

/-- A balanced honest sign times any bounded tag statistic has bias at most twice the distance. -/
theorem weightSign_mul_le_dist {Tag Out : Type*} [Fintype Tag] [Fintype Out]
    (p : Tag × Out → ℝ) (bit : Out → Bool)
    (balanced : mapWeight bit (uniformWeight Out) = uniformWeight Bool)
    (mask : Tag → ℝ) (bound : ∀ tag, |mask tag| ≤ 1) :
    |∑ z, p z * ((if bit z.2 then (1 : ℝ) else -1) * mask z.1)| ≤
      2 * weightDist p (uniformSecondWeight p) :=
  Internal.weightSign_mul_le_dist p bit balanced mask bound

/-- XOR with any tag-dependent bit preserves the twice-distance sign bound. -/
theorem weightSign_xor_le_dist {Tag Out : Type*} [Fintype Tag] [Fintype Out]
    (p : Tag × Out → ℝ) (bit : Out → Bool)
    (balanced : mapWeight bit (uniformWeight Out) = uniformWeight Bool)
    (mask : Tag → Bool) :
    |∑ z, p z * (if Bool.xor (bit z.2) (mask z.1) then (1 : ℝ) else -1)| ≤
      2 * weightDist p (uniformSecondWeight p) :=
  Internal.weightSign_xor_le_dist p bit balanced mask

/-- Every coordinate of a uniformly sampled Boolean vector is balanced. -/
theorem mapWeight_uniform_bool_coordinate {M : Nat} (j : Fin M) :
    mapWeight (fun x : Fin M → Bool => x j) (uniformWeight (Fin M → Bool)) =
      uniformWeight Bool :=
  Internal.mapWeight_uniform_bool_coordinate j

/-- Nonbad seeds bound the honest sign against every bounded tampered-output statistic. -/
theorem affineLeakage_sign_mul_le_of_not_mem_badSeeds {n d t : Nat}
    {Out : Type*} [Fintype Out]
    (cb : (Fin n → Bool) → (Fin d → Bool) → List Bool → Out)
    (p : (Fin n → Bool) → ℝ)
    (leak : (Fin n → Bool) → Option (Fin t) → Fin d → Bool)
    (advice : Option (Fin t) → List Bool) (γ : ℝ) (y : Fin d → Bool)
    (good : y ∉ affineLeakageBadSeeds cb p leak advice γ)
    (b : Fin n → Bool) (ys : Fin t → Fin d → Bool) (bit : Out → Bool)
    (balanced : mapWeight bit (uniformWeight Out) = uniformWeight Bool)
    (mask : (Fin t → Out) → ℝ) (bound : ∀ outputs, |mask outputs| ≤ 1) :
    |∑ x, p x *
      ((if bit (cb (xorInput x b) (xorInput y (leak x none)) (advice none))
        then (1 : ℝ) else -1) *
        mask (fun i => cb (xorInput x b)
          (xorInput (ys i) (leak x (some i))) (advice (some i))))| ≤ 2 * γ :=
  Internal.affineLeakage_sign_mul_le_of_not_mem_badSeeds
    cb p leak advice γ y good b ys bit balanced mask bound

/-- Nonbad seeds bound every XOR mask of the actual tampered outputs. -/
theorem affineLeakage_sign_le_of_not_mem_badSeeds {n d t : Nat}
    {Out : Type*} [Fintype Out]
    (cb : (Fin n → Bool) → (Fin d → Bool) → List Bool → Out)
    (p : (Fin n → Bool) → ℝ)
    (leak : (Fin n → Bool) → Option (Fin t) → Fin d → Bool)
    (advice : Option (Fin t) → List Bool) (γ : ℝ) (y : Fin d → Bool)
    (good : y ∉ affineLeakageBadSeeds cb p leak advice γ)
    (b : Fin n → Bool) (ys : Fin t → Fin d → Bool) (bit : Out → Bool)
    (balanced : mapWeight bit (uniformWeight Out) = uniformWeight Bool)
    (mask : (Fin t → Out) → Bool) :
    |∑ x, p x *
      (if Bool.xor
        (bit (cb (xorInput x b) (xorInput y (leak x none)) (advice none)))
        (mask (fun i => cb (xorInput x b)
          (xorInput (ys i) (leak x (some i))) (advice (some i))))
        then (1 : ℝ) else -1)| ≤ 2 * γ :=
  Internal.affineLeakage_sign_le_of_not_mem_badSeeds
    cb p leak advice γ y good b ys bit balanced mask

/-- Nonbad seeds bound every honest output coordinate after any tampered-output XOR mask. -/
theorem affineLeakage_coordinate_sign_le_of_not_mem_badSeeds {n d t M : Nat}
    (cb : (Fin n → Bool) → (Fin d → Bool) → List Bool → Fin M → Bool)
    (p : (Fin n → Bool) → ℝ)
    (leak : (Fin n → Bool) → Option (Fin t) → Fin d → Bool)
    (advice : Option (Fin t) → List Bool) (γ : ℝ) (y : Fin d → Bool)
    (good : y ∉ affineLeakageBadSeeds cb p leak advice γ)
    (b : Fin n → Bool) (ys : Fin t → Fin d → Bool) (j : Fin M)
    (mask : (Fin t → Fin M → Bool) → Bool) :
    |∑ x, p x *
      (if Bool.xor
        (cb (xorInput x b) (xorInput y (leak x none)) (advice none) j)
        (mask (fun i => cb (xorInput x b)
          (xorInput (ys i) (leak x (some i))) (advice (some i))))
        then (1 : ℝ) else -1)| ≤ 2 * γ :=
  Internal.affineLeakage_coordinate_sign_le_of_not_mem_badSeeds
    cb p leak advice γ y good b ys j mask

end Algebraic.Cutwidth.Extractor
