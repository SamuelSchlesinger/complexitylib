/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Sampler.Amplification.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Moments.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.SourceReduction.BadSeeds
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic.Linarith

/-!
# Good source fixings supplied by a somewhere sampler

Apply the sampler to the uniform weights on the second-source support.
The complement of its bad inputs retains at least a `1 - δ` fraction of
the support, and on each retained input at most a `2ε` fraction of outer
coordinates has all candidate seeds in the test set.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

open scoped Classical

theorem somewhereSampler_exists_good_fibers {α Outer Candidate Ω : Type*}
    [Fintype α] [Fintype Outer] [Fintype Ω]
    {S : α → Outer → Candidate → Ω} {L ε δ : ℝ}
    (sampler : SomewhereSampler S L ε δ) (Q : Finset α)
    (positive : 0 < Q.card) (source : L ≤ Q.card)
    (T : Finset Ω) (small : (T.card : ℝ) ≤ ε * Fintype.card Ω) :
    ∃ G ⊆ Q, (1 - δ) * Q.card ≤ G.card ∧
      ∀ y ∈ G, ((allHitSeeds S T y).card : ℝ) ≤ 2 * ε * Fintype.card Outer := by
  have hQ : (0 : ℝ) < Q.card := by exact_mod_cast positive
  let p : α → ℝ := fun y => if y ∈ Q then 1 / (Q.card : ℝ) else 0
  have nonneg : ∀ y, 0 ≤ p y := by
    intro y
    dsimp only [p]
    split <;> positivity
  have mass : ∑ y, p y = 1 := by
    simp [p, div_eq_mul_inv, ne_of_gt hQ]
  have cap : ∀ y, L * p y ≤ 1 := by
    intro y
    by_cases hy : y ∈ Q
    · simpa [p, hy, div_eq_mul_inv] using (div_le_one hQ).mpr source
    · simp [p, hy]
  have failure := sampler T small p nonneg mass cap
  have count : (∑ y ∈ somewhereBadInputs S T ε, p y) =
      (Q ∩ somewhereBadInputs S T ε).card / (Q.card : ℝ) := by
    simp [p, Finset.inter_comm, div_eq_mul_inv]
  rw [count] at failure
  have badBound := (div_le_iff₀ hQ).mp failure
  refine ⟨Q \ somewhereBadInputs S T ε, Finset.sdiff_subset, ?_, ?_⟩
  · have partition : ((Q \ somewhereBadInputs S T ε).card : ℝ) +
        (Q ∩ somewhereBadInputs S T ε).card = Q.card := by
      exact_mod_cast Finset.card_sdiff_add_card_inter Q (somewhereBadInputs S T ε)
    nlinarith only [badBound, partition]
  · intro y hy
    have outside := (Finset.mem_sdiff.mp hy).2
    simpa only [somewhereBadInputs, Finset.mem_filter, Finset.mem_univ, true_and,
      not_lt] using outside

theorem parityBiasBound_of_seed_escape {α Choice Seed : Type*} [Fintype Choice]
    {m N : Nat} {s : Finset α} {w : α → ℝ} {σ : α → Fin N → ℝ} {β : ℝ}
    (S : Fin N → Choice → Seed) (bad : Finset (Fin N) → Choice → Finset Seed)
    (good : Fin m ↪ Fin N)
    (escape : ∀ i, ∃ z, S (good i) z ∉ parityBadSeeds bad 4)
    (estimate : ∀ U ∈ parityTests (Fin N) 4, ∃ j ∈ U, ∀ z,
      S j z ∉ bad U z → |weightedMean s w (fun x => ∏ i ∈ U, σ x i)| ≤ β) :
    ParityBiasBound s w (fun x i => σ x (good i)) β := by
  intro T hT ht
  have imageMem : T.image good ∈ parityTests (Fin N) 4 := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, hT.image good, ?_⟩
    simpa only [Finset.card_image_of_injective _ good.injective] using ht
  obtain ⟨j, hj, bound⟩ := estimate (T.image good) imageMem
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hj
  obtain ⟨z, hz⟩ := escape i
  have outside : S (good i) z ∉ bad (T.image good) z := by
    intro inside
    apply hz
    exact Finset.mem_biUnion.mpr ⟨T.image good, imageMem,
      Finset.mem_biUnion.mpr ⟨z, Finset.mem_univ _, inside⟩⟩
  have h := bound z outside
  simpa only [Finset.prod_image good.injective.injOn] using h

theorem somewhereSampler_parity_fibers {α Source Choice Seed : Type*}
    [Fintype Source] [Fintype Choice] [Fintype Seed] {N : Nat}
    {s : Finset α} {w : α → ℝ} (σ : α → Source → Fin N → ℝ)
    {S : Source → Fin N → Choice → Seed} {L ε δ β η : ℝ}
    (sampler : SomewhereSampler S L ε δ) (Q : Finset Source)
    (positive : 0 < Q.card) (source : L ≤ Q.card)
    (bad : Finset (Fin N) → Choice → Finset Seed) (nonneg : 0 ≤ η)
    (seedBound : ∀ U ∈ parityTests (Fin N) 4, ∀ z,
      ((bad U z).card : ℝ) ≤ η * Fintype.card Seed)
    (budget : (N : ℝ) ^ 4 * Fintype.card Choice * η ≤ ε)
    (estimate : ∀ U ∈ parityTests (Fin N) 4, ∃ j ∈ U, ∀ z, ∀ y ∈ Q,
      S y j z ∉ bad U z →
        |weightedMean s w (fun x => ∏ i ∈ U, σ x y i)| ≤ β) :
    ∃ G ⊆ Q, (1 - δ) * Q.card ≤ G.card ∧
      ∀ y ∈ G, ∃ (m : Nat) (good : Fin m ↪ Fin N),
        ((N - m : Nat) : ℝ) ≤ 2 * ε * N ∧
        ParityBiasBound s w (fun x i => σ x y (good i)) β := by
  have small : ((parityBadSeeds bad 4).card : ℝ) ≤ ε * Fintype.card Seed := by
    have bound := card_parityBadSeeds_le bad 4 nonneg seedBound
    simp only [Fintype.card_fin] at bound
    exact bound.trans (mul_le_mul_of_nonneg_right budget (Nat.cast_nonneg _))
  obtain ⟨G, inside, many, goodFibers⟩ :=
    somewhereSampler_exists_good_fibers sampler Q positive source (parityBadSeeds bad 4) small
  refine ⟨G, inside, many, ?_⟩
  intro y hy
  let U := Finset.univ \ allHitSeeds S (parityBadSeeds bad 4) y
  let good : Fin U.card ↪ Fin N := (U.orderEmbOfFin rfl).toEmbedding
  refine ⟨U.card, good, ?_, ?_⟩
  · have partition : U.card + (allHitSeeds S (parityBadSeeds bad 4) y).card = N := by
      simpa only [U, Finset.univ_inter, Finset.card_univ, Fintype.card_fin] using
        Finset.card_sdiff_add_card_inter Finset.univ (allHitSeeds S (parityBadSeeds bad 4) y)
    have count : N - U.card = (allHitSeeds S (parityBadSeeds bad 4) y).card := by lia
    rw [count]
    simpa only [Fintype.card_fin] using goodFibers y hy
  · apply parityBiasBound_of_seed_escape (fun i z => S y i z) bad good
    · intro i
      have hmem : good i ∈ U := U.orderEmbOfFin_mem rfl i
      have hout := (Finset.mem_sdiff.mp hmem).2
      simpa only [allHitSeeds, Finset.mem_filter, Finset.mem_univ, true_and,
        not_forall] using hout
    · intro T hT
      obtain ⟨j, hj, bound⟩ := estimate T hT
      exact ⟨j, hj, fun z => bound z y (inside hy)⟩

end Algebraic.Cutwidth.Extractor.Internal
