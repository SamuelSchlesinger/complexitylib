/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.SourceReduction.Tests.Defs
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.SourceReduction.Tests.Internal

/-!
# Actual seed tests for all fourth-order source-reduction parities

The complete fixed affine construction at `4 * C - 1` tamperings supplies
one family of small bad-seed sets. Each parity test chooses its honest
outer coordinate before the candidate and second summand are supplied.
The estimate is for the actual XOR reduction and holds at every fixing.

This is the fixed-family parity step of Chattopadhyay--Liao, *Extractors
for Sum of Two Sources*, Lemma 5.4, equation (5):
<https://arxiv.org/abs/2110.12652>. The original source pays the complete
leakage reserve. Unused proof-side tampering slots have zero leakage and
same-length advice differing from the honest advice; their outputs do not
enter the parity mask. No sampler or security theorem is a premise.
-/

public section

namespace Algebraic.Cutwidth.Extractor

/-- Original source hypotheses give small tests and the exact all-fixings parity estimate. -/
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
            (fun i k => advice (i, k)) (xorInput x b) i then (1 : ℝ) else -1)| ≤ 2 * γ :=
  Internal.affineSourceReduction_exists_tests n N C a target p S advice candidates
    advice_positive error probability cap length injective linear

end Algebraic.Cutwidth.Extractor
