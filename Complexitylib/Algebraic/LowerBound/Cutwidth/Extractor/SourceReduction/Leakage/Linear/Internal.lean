/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.SourceReduction.Leakage.Parity

/-!
# Linear sampler outputs turn leakage bounds into parity bounds

After fixing the second summand, linearity expresses each actual sampler
seed as the XOR of a fixed seed and a source observation. The honest
output controls the full product of signs of the selected calls.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

theorem affineLeakage_linear_parity_le {n d t : Nat} {Out : Type*} [Fintype Out]
    (cb : (Fin n → Bool) → (Fin d → Bool) → List Bool → Out)
    (p : (Fin n → Bool) → ℝ)
    (sampler : (Fin n → Bool) → Option (Fin t) → Fin d → Bool)
    (advice : Option (Fin t) → List Bool)
    (linear : ∀ x y i, sampler (xorInput x y) i = xorInput (sampler x i) (sampler y i))
    (bit : Out → Bool) (balanced : mapWeight bit (uniformWeight Out) = uniformWeight Bool)
    (γ : ℝ) (b : Fin n → Bool)
    (good : sampler b none ∉ affineLeakageBadSeeds cb p sampler advice γ) :
    |∑ x, p x * ∏ i, if bit (cb (xorInput x b) (sampler (xorInput x b) i) (advice i))
      then (1 : ℝ) else -1| ≤ 2 * γ := by
  let mask := fun outputs : Fin t → Out => ∏ i, if bit (outputs i) then (1 : ℝ) else -1
  have bound (outputs : Fin t → Out) : |mask outputs| ≤ 1 := by
    dsimp only [mask]
    rw [Finset.abs_prod]
    have sign (i : Fin t) : |if bit (outputs i) then (1 : ℝ) else -1| = 1 := by
      cases bit (outputs i) <;> norm_num
    simp only [sign, Finset.prod_const_one, le_refl]
  have estimate := affineLeakage_sign_mul_le_of_not_mem_badSeeds cb p sampler advice γ
    (sampler b none) good b (fun i => sampler b (some i)) bit balanced mask bound
  have seed (x : Fin n → Bool) (i : Option (Fin t)) :
      xorInput (sampler b i) (sampler x i) = sampler (xorInput x b) i := by
    rw [linear]
    funext j
    exact Bool.xor_comm _ _
  simpa only [mask, seed, Fintype.prod_option] using estimate

end Algebraic.Cutwidth.Extractor.Internal
