/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Defs
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Aggregating good second-source fixings

Conditional outcome mass on a large set of second-source inputs gives
unconditional outcome mass on the product of the source sets. Counting
ordered pairs keeps repeated XOR values with their original multiplicity.
This is the finite averaging step after the majority analysis in the
Chattopadhyay–Liao sumset-extractor route.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

open scoped Classical

private theorem card_outcome_product {α β : Type*} (P : Finset α) (Q : Finset β)
    (f : α → β → Bool) (b : Bool) :
    ((P ×ˢ Q).filter fun xy => f xy.1 xy.2 = b).card =
      ∑ y ∈ Q, (P.filter fun x => f x y = b).card := by
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter, Finset.sum_product]
  rw [Finset.sum_comm]

private theorem card_outcome_ge_of_good_fibers {α β : Type*}
    (P : Finset α) (Q G : Finset β) (f : α → β → Bool) (b : Bool)
    (positive : 0 < P.card) (inside : G ⊆ Q) {ρ θ : ℝ} (hρ : 0 ≤ ρ)
    (many : θ * Q.card ≤ G.card)
    (fibers : ∀ y ∈ G, ρ ≤ ∑ x ∈ P, if f x y = b then 1 / (P.card : ℝ) else 0) :
    ρ * θ * (P.card * Q.card) ≤
      (((P ×ˢ Q).filter fun xy => f xy.1 xy.2 = b).card : ℝ) := by
  have positiveReal : (0 : ℝ) < P.card := by exact_mod_cast positive
  have row : ∀ y ∈ G, ρ * P.card ≤ ((P.filter fun x => f x y = b).card : ℝ) := by
    intro y hy
    have count : (∑ x ∈ P, if f x y = b then 1 / (P.card : ℝ) else 0) =
        (P.filter fun x => f x y = b).card / (P.card : ℝ) := by
      rw [← Finset.sum_filter]
      simp [div_eq_mul_inv]
    have bound := fibers y hy
    rw [count] at bound
    exact (le_div_iff₀ positiveReal).mp bound
  calc
    ρ * θ * (P.card * Q.card) = (ρ * P.card) * (θ * Q.card) := by ring
    _ ≤ (ρ * P.card) * G.card :=
      mul_le_mul_of_nonneg_left many (mul_nonneg hρ (Nat.cast_nonneg _))
    _ = ∑ _y ∈ G, ρ * P.card := by simp [mul_comm]
    _ ≤ ∑ y ∈ G, ((P.filter fun x => f x y = b).card : ℝ) :=
      Finset.sum_le_sum row
    _ ≤ ∑ y ∈ Q, ((P.filter fun x => f x y = b).card : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg inside (fun _ _ _ => Nat.cast_nonneg _)
    _ = (((P ×ˢ Q).filter fun xy => f xy.1 xy.2 = b).card : ℝ) := by
      exact_mod_cast (card_outcome_product P Q f b).symm

theorem flatSumsetExtractor_of_many_good_fibers {n K : Nat}
    {f : Cslib.BooleanFunction n} {ρ θ : ℝ} (positive : 0 < K) (hρ : 0 ≤ ρ)
    (good : ∀ P Q : Finset (Fin n → Bool), K ≤ P.card → K ≤ Q.card →
      ∃ G ⊆ Q, θ * Q.card ≤ G.card ∧
        ∀ y ∈ G, ∀ b : Bool,
          ρ ≤ ∑ x ∈ P, if f (xorInput x y) = b then 1 / (P.card : ℝ) else 0) :
    FlatSumsetExtractor f K (1 / 2 - ρ * θ) := by
  intro P Q hP hQ
  obtain ⟨G, inside, many, fibers⟩ := good P Q hP hQ
  have trueCount := card_outcome_ge_of_good_fibers P Q G (fun x y => f (xorInput x y))
    true (positive.trans_le hP) inside hρ many (fun y hy => fibers y hy true)
  have falseCount := card_outcome_ge_of_good_fibers P Q G (fun x y => f (xorInput x y))
    false (positive.trans_le hP) inside hρ many (fun y hy => fibers y hy false)
  have total : ((sumsetOnes f P Q).card : ℝ) +
      (((P ×ˢ Q).filter fun xy => f (xorInput xy.1 xy.2) = false).card : ℝ) =
        (P.card : ℝ) * Q.card := by
    have partition := Finset.card_filter_add_card_filter_not
      (s := P ×ˢ Q) (p := fun xy => f (xorInput xy.1 xy.2) = true)
    simp only [Bool.not_eq_true, Finset.card_product] at partition
    exact_mod_cast partition
  change ρ * θ * ((P.card : ℝ) * Q.card) ≤ (sumsetOnes f P Q).card at trueCount
  constructor <;> nlinarith only [trueCount, falseCount, total]

end Algebraic.Cutwidth.Extractor.Internal
