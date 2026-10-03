/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Encoding.Explicit.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Condenser.Defs
public import Mathlib.Data.Fintype.Pi
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Encoding.Explicit.Lossless
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Condenser
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Lossless.Mixture.Internal
import Mathlib.Data.List.OfFn

/-!
# Transporting the scheduled condenser to weighted inputs

An injective representation preserves exact support cardinality and uniform
test probabilities. Transport the scheduled condenser's seedwise injection
witnesses along that equivalence, then apply the finite flat-mixture theorem.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

open scoped Classical

private theorem seededTestProb_comp_equiv {α β Seed Ω : Type*}
    [Fintype α] [Fintype β] [Fintype Seed] (e : α ≃ β)
    (C : β → Seed → Ω) (T : Finset (Seed × Ω)) :
    seededTestProb (fun x => C (e x)) T = seededTestProb C T := by
  rw [seededTestProb_eq_sum, seededTestProb_eq_sum, Fintype.card_congr e]
  congr 1
  exact e.sum_comp (fun x =>
    ((Finset.univ.filter fun y => (y, C x y) ∈ T).card : ℝ))

theorem decodedExplicitCondenser_weighted (n k e u : Nat) {α : Type*} [Fintype α]
    [Fintype (AdjoinRoot
      (binaryModulus (sparseFieldExponent u (explicitCondenserBudget n k e))))]
    (rate : 0 < u) (input : α ↪ List Bool) (source : ∀ x, (input x).length = n) :
    WeightedStrongSeededCondenser
      (fun x => decodedExplicitCondenser n k e u (input x)) (2 ^ k) (2 ^ k)
      ((2 : ℝ) ^ e)⁻¹ := by
  apply weightedStrongSeededCondenser_of_flat_injections _ (by positivity)
  intro P cardinality
  have nonempty : (P.map input).Nonempty := by
    apply Finset.card_pos.mp
    rw [Finset.card_map, cardinality]
    positivity
  have length : ∀ bits ∈ P.map input, bits.length = n := by
    intro bits member
    obtain ⟨x, _, rfl⟩ := Finset.mem_map.mp member
    exact source x
  obtain ⟨g, close⟩ := decodedExplicitCondenser_flat_lossless n k e u rate
    (P.map input) nonempty length (by simp only [Finset.card_map, cardinality, le_refl])
  let repr := Finset.equivMap input P
  refine ⟨fun y => repr.toEmbedding.trans (g y), fun T => ?_⟩
  have actual := seededTestProb_comp_equiv repr
    (fun bits : P.map input => decodedExplicitCondenser n k e u bits.val) T
  have ideal := seededTestProb_comp_equiv repr (fun bits y => g y bits) T
  change |seededTestProb (fun x => decodedExplicitCondenser n k e u (repr x).val) T -
    seededTestProb (fun x y => g y (repr x)) T| ≤ _
  rw [actual, ideal]
  exact close T

theorem decodedExplicitCondenser_weighted_ofFn (n k e u : Nat)
    [Fintype (AdjoinRoot
      (binaryModulus (sparseFieldExponent u (explicitCondenserBudget n k e))))]
    (rate : 0 < u) :
    WeightedStrongSeededCondenser
      (fun x : Fin n → Bool => decodedExplicitCondenser n k e u (List.ofFn x))
      (2 ^ k) (2 ^ k) ((2 : ℝ) ^ e)⁻¹ :=
  decodedExplicitCondenser_weighted n k e u rate
    ⟨List.ofFn, List.ofFn_injective⟩ (fun _ => List.length_ofFn)

end Algebraic.Cutwidth.Extractor.Internal
