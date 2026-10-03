/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Advice.Extraction.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Affine.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Conditional.Defs
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Advice.Internal.Invariant.Initial
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.LookAhead.UniformState

/-!
# The actual initial state supplied by a uniform right source

The full right input is retained and can be correlated with its tampered
copy. Uniformity of the honest right input supplies its exact source
envelope and a uniform initial-state prefix. No intermediate state or
extractor property is assumed.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

theorem adviceInitialState_retained_dist (m L : Nat) {Z B : Type*}
    [Fintype Z] [Fintype B] (w : Z → ℝ) (r : Z → B → ℝ)
    (y : Z → B → Fin m → Bool) (size : matchedBlockOutputBits 64 L ≤ m)
    (uniform : ∀ z, mapWeight (y z) (r z) = uniformWeight (Fin m → Bool)) :
    weightDist (retainedSeedWeight w r (fun z b => adviceInitialState m L (y z b)))
      (uniformSecondWeight
        (retainedSeedWeight w r (fun z b => adviceInitialState m L (y z b)))) = 0 :=
  retainedSeedWeight_uniform_image_dist w r y (adviceInitialState m L)
    (adviceInitialState_uniform m L size) (fun z _ => by rw [uniform z])

theorem adviceUniformRight_cap (m : Nat) {Z B : Type*} [Fintype B]
    (w : Z → ℝ) (r : Z → B → ℝ) (y : Z → B → Fin m → Bool)
    (uniform : ∀ z, mapWeight (y z) (r z) = uniformWeight (Fin m → Bool))
    (z : Z) (y₀ : Fin m → Bool) :
    w z * mapWeight (y z) (r z) y₀ = w z * ((2 : ℝ) ^ m)⁻¹ := by
  rw [uniform z]
  simp only [uniformWeight, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin,
    Nat.cast_pow, Nat.cast_ofNat]

theorem adviceUniformRight_sum (m : Nat) {Z : Type*} [Fintype Z]
    (w : Z → ℝ) (hw : IsProbabilityWeight w) :
    (∑ z, w z * ((2 : ℝ) ^ m)⁻¹) = ((2 : ℝ) ^ m)⁻¹ := by
  rw [← Finset.sum_mul, hw.2, one_mul]

end Algebraic.Cutwidth.Extractor.Internal
