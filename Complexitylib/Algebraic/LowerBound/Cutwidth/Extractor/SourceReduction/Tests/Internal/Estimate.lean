/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.SourceReduction.Tests.Defs
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.SourceReduction.Tests.Internal.Slots
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.SourceReduction.Leakage
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.SourceReduction.Leakage.Parity
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.SourceReduction.Reduction
import Mathlib.Tactic.NormNum

/-!
# One small parity test for the fixed actual breaker

Only the genuinely used slots enter the product mask. Padding changes
neither the reduction nor its parity. Every seed test is obtained from
the actual selected correlation breaker and its original source reserve.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

theorem exists_affineSourceTest (n N C a target : Nat)
    (p : (Fin n → Bool) → ℝ)
    (S : (Fin n → Bool) → Fin N → Fin C → Fin (affineTestSeedBits n C a target) → Bool)
    (advice : Fin N × Fin C → List Bool) {γ : ℝ}
    (candidates : 0 < C) (advice_positive : 0 < a) (error : 0 < γ)
    (probability : IsProbabilityWeight p)
    (cap : ∀ x, p x ≤ ((2 : ℝ) ^ affineLeakageSourceEntropy n (4 * C - 1) a target)⁻¹)
    (length : ∀ v, (advice v).length = a) (injective : Function.Injective advice)
    (linear : ∀ x y i z, S (xorInput x y) i z = xorInput (S x i z) (S y i z))
    (U : Finset (Fin N)) (small : U.card ≤ 4) (j : Fin N) (member : j ∈ U) (z : Fin C) :
    ∃ bad : Finset (Fin (affineTestSeedBits n C a target) → Bool),
      ((bad.card : ℝ) ≤ (((2 : ℝ) ^ target)⁻¹ / γ) *
        Fintype.card (Fin (affineTestSeedBits n C a target) → Bool)) ∧
      ∀ b, S b j z ∉ bad →
        |weightedMean Finset.univ p (fun x => ∏ i ∈ U,
          if affineSourceReduction (affineTestBit n C a target) S
            (fun i k => advice (i, k)) (xorInput x b) i then (1 : ℝ) else -1)| ≤ 2 * γ := by
  classical
  let Others := affineTestOtherSlots U j z
  obtain ⟨embedding⟩ : Nonempty (Others ↪ Fin (4 * C - 1)) :=
    Function.Embedding.nonempty_of_card_le (affineTestOtherSlots_card U small j member z)
  let leak := fun (x : Fin n → Bool) (i : Option (Fin (4 * C - 1))) =>
    match i with
    | none => S x j z
    | some k => affineTestPadded embedding (fun v => S x v.1.1 v.1.2) (fun _ => false) k
  let adv := fun i : Option (Fin (4 * C - 1)) =>
    match i with
    | none => advice (j, z)
    | some k => affineTestPadded embedding (fun v => advice v.1)
        (affineTestDummyAdvice (advice (j, z))) k
  have honest_length : (adv none).length = a := length (j, z)
  have tampered_length (i : Fin (4 * C - 1)) : (adv (some i)).length = a := by
    exact affineTestPadded_property embedding _ _ (fun word : List Bool => word.length = a)
      (fun v => length v.1) (by rw [affineTestDummyAdvice_length, length]) i
  have different (i : Fin (4 * C - 1)) : adv none ≠ adv (some i) := by
    apply affineTestPadded_property embedding _ _ (fun word => advice (j, z) ≠ word)
    · intro v equal
      have same := injective equal
      exact affineTestOtherSlots_ne U j z v same.symm
    · apply affineTestDummyAdvice_ne
      rw [length]
      exact advice_positive
  let bad := affineLeakageBadSeeds (affineTestBreaker n C a target) p leak adv γ
  refine ⟨bad, ?_, ?_⟩
  · exact affineLeakageBadSeeds_parameters_card_le n (4 * C - 1) a target p leak adv
      (by lia) error probability cap honest_length tampered_length different
  · intro b good
    let bit := fun output : Fin (affineTestOutputBits n C a target) → Bool =>
      output (affineTestFirst n C a target)
    let mask := fun outputs : Fin (4 * C - 1) → Fin (affineTestOutputBits n C a target) → Bool =>
      ∏ v : Others, if bit (outputs (embedding v)) then (1 : ℝ) else -1
    have bounded (outputs) : |mask outputs| ≤ 1 := by
      dsimp only [mask]
      rw [Finset.abs_prod]
      have signs (v : Others) : |if bit (outputs (embedding v)) then (1 : ℝ) else -1| = 1 := by
        cases bit (outputs (embedding v)) <;> norm_num
      simp only [signs, Finset.prod_const_one, le_refl]
    have estimate := affineLeakage_sign_mul_le_of_not_mem_badSeeds
      (affineTestBreaker n C a target) p leak adv γ (S b j z) good b
      (fun i => leak b (some i)) bit (mapWeight_uniform_bool_coordinate _) mask bounded
    have seeds (x : Fin n → Bool) (i : Fin N) (k : Fin C) :
        xorInput (S b i k) (S x i k) = S (xorInput x b) i k := by
      rw [linear]
      funext q
      exact Bool.xor_comm _ _
    have integrand (x : Fin n → Bool) :
        ((if bit (affineTestBreaker n C a target (xorInput x b)
          (xorInput (S b j z) (leak x none)) (adv none)) then (1 : ℝ) else -1) *
          mask (fun i => affineTestBreaker n C a target (xorInput x b)
            (xorInput (leak b (some i)) (leak x (some i))) (adv (some i)))) =
          ∏ i ∈ U, ∏ k, if affineTestBit n C a target (xorInput x b)
            (S (xorInput x b) i k) (advice (i, k)) then (1 : ℝ) else -1 := by
      dsimp only [mask, leak, adv]
      simp only [affineTestPadded_apply, seeds]
      exact affineTestOtherSlots_prod U j member z
        (fun v => if affineTestBit n C a target (xorInput x b)
          (S (xorInput x b) v.1 v.2) (advice v) then (1 : ℝ) else -1)
    simp only [integrand] at estimate
    rw [affineSourceReduction_parity_bias_eq]
    exact estimate

end Algebraic.Cutwidth.Extractor.Internal
