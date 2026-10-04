/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.SourceReduction.Tests.Defs
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.SourceReduction.Tests.Internal.Estimate

/-!
# A simultaneous family of fixed-budget seed tests

Choose a distinguished coordinate separately for each nonempty parity
test, before any candidate or source shift is supplied. The resulting
bad-seed family has precisely the quantifier order needed by the global
somewhere-sampler selection theorem.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

theorem affineSourceReduction_exists_tests (n N C a target : Nat)
    (p : (Fin n → Bool) → ℝ)
    (S : (Fin n → Bool) → Fin N → Fin C → Fin (affineTestSeedBits n C a target) → Bool)
    (advice : Fin N × Fin C → List Bool) {γ : ℝ}
    (candidates : 0 < C) (advice_positive : 0 < a) (error : 0 < γ)
    (probability : IsProbabilityWeight p)
    (cap : ∀ x, p x ≤ ((2 : ℝ) ^ affineLeakageSourceEntropy n (4 * C - 1) a target)⁻¹)
    (length : ∀ v, (advice v).length = a) (injective : Function.Injective advice)
    (linear : ∀ x y i z, S (xorInput x y) i z = xorInput (S x i z) (S y i z)) :
    ∃ bad : Finset (Fin N) → Fin C → Finset (Fin (affineTestSeedBits n C a target) → Bool),
      (∀ U ∈ parityTests (Fin N) 4, ∀ z,
        ((bad U z).card : ℝ) ≤ (((2 : ℝ) ^ target)⁻¹ / γ) *
          Fintype.card (Fin (affineTestSeedBits n C a target) → Bool)) ∧
      ∀ U ∈ parityTests (Fin N) 4, ∃ j ∈ U, ∀ z b, S b j z ∉ bad U z →
        |weightedMean Finset.univ p (fun x => ∏ i ∈ U,
          if affineSourceReduction (affineTestBit n C a target) S
            (fun i k => advice (i, k)) (xorInput x b) i then (1 : ℝ) else -1)| ≤ 2 * γ := by
  classical
  have each (U : Finset (Fin N)) (test : U ∈ parityTests (Fin N) 4) :
      ∃ j ∈ U, ∃ bad : Fin C → Finset (Fin (affineTestSeedBits n C a target) → Bool),
        (∀ z, ((bad z).card : ℝ) ≤ (((2 : ℝ) ^ target)⁻¹ / γ) *
          Fintype.card (Fin (affineTestSeedBits n C a target) → Bool)) ∧
        ∀ z b, S b j z ∉ bad z →
          |weightedMean Finset.univ p (fun x => ∏ i ∈ U,
            if affineSourceReduction (affineTestBit n C a target) S
              (fun i k => advice (i, k)) (xorInput x b) i then (1 : ℝ) else -1)| ≤ 2 * γ := by
    obtain ⟨nonempty, small⟩ := (Finset.mem_filter.mp test).2
    obtain ⟨j, member⟩ := nonempty
    have single (z : Fin C) := exists_affineSourceTest n N C a target p S advice
      candidates advice_positive error probability cap length injective linear U small j member z
    choose bad cardinal estimate using single
    exact ⟨j, member, bad, cardinal, estimate⟩
  choose j member bad cardinal estimate using each
  refine ⟨fun U z => if h : U ∈ parityTests (Fin N) 4 then bad U h z else ∅, ?_, ?_⟩
  · intro U test z
    simpa only [dite_eq_left test] using cardinal U test z
  · intro U test
    refine ⟨j U test, member U test, ?_⟩
    intro z b good
    exact estimate U test z b (by simpa only [dite_eq_left test] using good)

end Algebraic.Cutwidth.Extractor.Internal
