/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Encoding.Correctness.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Lossless.Mixture.Defs
public import Mathlib.Data.Fintype.Pi
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Encoding.Correctness
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Expansion
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Lossless
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Lossless.Mixture
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Modulus.Binary
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# Flat lossless guarantees for the decoded runtime condenser

Within the coefficient capacity, equal-length bitstrings give distinct source
polynomials. The runtime correctness theorem therefore transfers polynomial
neighbor expansion without collapsing any source points. The seedwise
injection theorem turns this expansion into a bound on every retained-seed
test, and exact subset averaging extends it to larger flat supports.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

open scoped Classical

theorem decodedCondenser_flat_lossless (s v n : Nat)
    [Fintype (AdjoinRoot (binaryModulus s))]
    (halfDegree extensionCount stride count : List Bool)
    (half : halfDegree.length = 3 ^ s) (extension : extensionCount.length = 3 ^ v)
    (degree : 0 < v) (fieldSize : stride.length ≤ 2 * 3 ^ s)
    (capacity : n ≤ (2 * 3 ^ s) * 3 ^ v)
    (P : Finset (List Bool)) (nonempty : P.Nonempty)
    (source : ∀ bits ∈ P, bits.length = n)
    (size : P.card ≤ (2 ^ stride.length) ^ count.length) :
    ∃ g : AdjoinRoot (binaryModulus s) →
        (P ↪ (Fin count.length → AdjoinRoot (binaryModulus s))),
      ∀ T : Finset (AdjoinRoot (binaryModulus s) ×
          (Fin count.length → AdjoinRoot (binaryModulus s))),
        |seededTestProb
            (fun bits : P => decodedCondenser s halfDegree extensionCount stride count bits.val) T -
          seededTestProb (fun bits y => g y bits) T| ≤
            (((3 ^ v - 1) * (2 ^ stride.length - 1) * count.length : Nat) : ℝ) /
              (2 : ℝ) ^ (2 * 3 ^ s) := by
  let : Fact (Irreducible (binaryModulus s)) := ⟨binaryModulus_irreducible s⟩
  have fieldCard : Fintype.card (AdjoinRoot (binaryModulus s)) = 2 ^ (2 * 3 ^ s) := by
    simpa only [Nat.card_eq_fintype_card] using card_adjoinRoot_binaryModulus s
  have sourceCard : (P.image (sourcePolynomial s (3 ^ v))).card = P.card := by
    apply Finset.card_image_iff.mpr
    intro a ha b hb same
    exact sourcePolynomial_inj_of_length s v n capacity a b (source a ha) (source b hb) same
  have outputCapacity : P.card ≤
      Fintype.card (Fin count.length → AdjoinRoot (binaryModulus s)) := by
    rw [Fintype.card_fun, Fintype.card_fin, fieldCard]
    exact size.trans (Nat.pow_le_pow_left (Nat.pow_le_pow_right (by decide) fieldSize) _)
  have neighbors : seededNeighborSet
      (decodedCondenser s halfDegree extensionCount stride count) P =
        polynomialNeighborSet (extensionModulus s v) (2 ^ stride.length) count.length
          (P.image (sourcePolynomial s (3 ^ v))) := by
    unfold seededNeighborSet polynomialNeighborSet
    rw [Finset.image_biUnion]
    ext z
    simp only [Finset.mem_biUnion, Finset.mem_image, polynomialNeighbor_pow_two,
      decodedCondenser_eq s v _ _ _ _ _ _ half extension]
  have sourceDegree : ∀ f ∈ P.image (sourcePolynomial s (3 ^ v)),
      f.degree < (extensionModulus s v).degree := by
    intro f hf
    obtain ⟨bits, _, rfl⟩ := Finset.mem_image.mp hf
    rw [Polynomial.degree_eq_natDegree (extensionModulus_monic s v).ne_zero,
      extensionModulus_natDegree]
    exact sourcePolynomial_degree_lt s (3 ^ v) bits
  have expansion := polynomialNeighborSet_expansion (extensionModulus s v)
    (extensionModulus_monic s v) (extensionModulus_irreducible s v)
    (by rw [extensionModulus_natDegree]; exact Nat.one_lt_pow (by lia) (by decide))
    (Nat.two_pow_pos stride.length) (P.image (sourcePolynomial s (3 ^ v)))
    sourceDegree (by simpa only [sourceCard] using size)
  rw [sourceCard, extensionModulus_natDegree, ← neighbors] at expansion
  apply exists_seedwise_injection_of_expansion
    (decodedCondenser s halfDegree extensionCount stride count) P nonempty outputCapacity
  let loss := (3 ^ v - 1) * (2 ^ stride.length - 1) * count.length
  have cover : (Fintype.card (AdjoinRoot (binaryModulus s)) : ℝ) ≤
      ((Fintype.card (AdjoinRoot (binaryModulus s)) - loss : Nat) : ℝ) + loss := by
    exact_mod_cast (le_tsub_add : Fintype.card (AdjoinRoot (binaryModulus s)) ≤
      Fintype.card (AdjoinRoot (binaryModulus s)) - loss + loss)
  have fieldCardReal : (Fintype.card (AdjoinRoot (binaryModulus s)) : ℝ) =
      (2 : ℝ) ^ (2 * 3 ^ s) := by
    rw [fieldCard, Nat.cast_pow, Nat.cast_ofNat]
  have factor : (1 - (loss : ℝ) / (2 : ℝ) ^ (2 * 3 ^ s)) *
      Fintype.card (AdjoinRoot (binaryModulus s)) =
        (Fintype.card (AdjoinRoot (binaryModulus s)) : ℝ) - loss := by
    rw [fieldCardReal]
    field_simp
  calc
    (1 - (loss : ℝ) / (2 : ℝ) ^ (2 * 3 ^ s)) * P.card *
        Fintype.card (AdjoinRoot (binaryModulus s)) =
          ((Fintype.card (AdjoinRoot (binaryModulus s)) : ℝ) - loss) * P.card := by
      rw [mul_right_comm, factor]
    _ ≤ ((Fintype.card (AdjoinRoot (binaryModulus s)) - loss : Nat) : ℝ) * P.card :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _ ≤ ((seededNeighborSet
        (decodedCondenser s halfDegree extensionCount stride count) P).card : ℝ) := by
      exact_mod_cast expansion

theorem decodedCondenser_flat_mixture (s v n : Nat)
    [Fintype (AdjoinRoot (binaryModulus s))]
    (halfDegree extensionCount stride count : List Bool)
    (half : halfDegree.length = 3 ^ s) (extension : extensionCount.length = 3 ^ v)
    (degree : 0 < v) (fieldSize : stride.length ≤ 2 * 3 ^ s)
    (capacity : n ≤ (2 * 3 ^ s) * 3 ^ v)
    (P : Finset (List Bool)) (source : ∀ bits ∈ P, bits.length = n) {K : Nat}
    (positive : 0 < K) (threshold : K ≤ P.card)
    (size : K ≤ (2 ^ stride.length) ^ count.length) :
    ∃ g : ∀ S : P.powersetCard K, AdjoinRoot (binaryModulus s) →
        (S.val ↪ (Fin count.length → AdjoinRoot (binaryModulus s))),
      ∀ T : Finset (AdjoinRoot (binaryModulus s) ×
          (Fin count.length → AdjoinRoot (binaryModulus s))),
        |seededTestProb
            (fun bits : P => decodedCondenser s halfDegree extensionCount stride count bits.val) T -
          seededMixtureTestProb (fun _ : P.powersetCard K =>
            ((P.powersetCard K).card : ℝ)⁻¹) (fun S bits y => g S y bits) T| ≤
            (((3 ^ v - 1) * (2 ^ stride.length - 1) * count.length : Nat) : ℝ) /
              (2 : ℝ) ^ (2 * 3 ^ s) := by
  apply exists_flat_mixture_of_exact_size
    (decodedCondenser s halfDegree extensionCount stride count) P positive threshold
  intro S subset card
  exact decodedCondenser_flat_lossless s v n halfDegree extensionCount stride count
    half extension degree fieldSize capacity S (Finset.card_pos.mp (card ▸ positive))
    (fun bits hbits => source bits (subset hbits)) (card ▸ size)

end Algebraic.Cutwidth.Extractor.Internal
