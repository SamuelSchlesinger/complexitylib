/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Sampler.Amplification.Defs
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Finite sampler amplification proofs

The neighbors of outer seeds whose every candidate hits a test lie in the
base sampler's hit set. Coverage therefore bounds the number of those outer
seeds. This pointwise implication transfers the arbitrary weighted failure
bound. Seeded extraction gives coverage by testing the full neighbor image.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

open scoped Classical

theorem card_allHitSeeds_lt {α Outer Candidate Base Ω : Type*}
    [Fintype Outer] [Fintype Candidate] [Fintype Base] [Nonempty Base]
    {Γ : Outer → Candidate → Base} {K : Nat} {ρ ε₀ : ℝ}
    (cover : NeighborCoverage Γ K ρ) (separate : 2 * ε₀ < ρ)
    (E : α → Base → Ω) (T : Finset Ω) (x : α)
    (good : (seedHits E T x : ℝ) ≤ 2 * ε₀ * Fintype.card Base) :
    (allHitSeeds (fun x y z => E x (Γ y z)) T x).card < K := by
  by_contra hn
  have hK : K ≤ (allHitSeeds (fun x y z => E x (Γ y z)) T x).card := by lia
  have hsub : neighborSet Γ (allHitSeeds (fun x y z => E x (Γ y z)) T x) ⊆
      Finset.univ.filter (fun y => E x y ∈ T) := by
    intro y hy
    obtain ⟨a, ha, hy⟩ := Finset.mem_biUnion.mp hy
    obtain ⟨z, _, rfl⟩ := Finset.mem_image.mp hy
    simp only [allHitSeeds, Finset.mem_filter, Finset.mem_univ, true_and] at ha
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha z⟩
  have hcard : ((neighborSet Γ
      (allHitSeeds (fun x y z => E x (Γ y z)) T x)).card : ℝ) ≤ seedHits E T x := by
    exact_mod_cast Finset.card_le_card hsub
  have hbase : (0 : ℝ) < Fintype.card Base := by exact_mod_cast Fintype.card_pos
  have hupper := (cover _ hK).trans (hcard.trans good)
  exact (not_le_of_gt (mul_lt_mul_of_pos_right separate hbase)) hupper

theorem neighborCoverage_of_flatSeededExtractor {Outer Candidate Base : Type*}
    [Fintype Candidate] [Nonempty Candidate] [Fintype Base]
    {Γ : Outer → Candidate → Base} {K : Nat} {ε : ℝ}
    (extract : FlatSeededExtractor Γ K ε) (positive : 0 < K) :
    NeighborCoverage Γ K (1 - ε) := by
  intro P hP
  have hits (y : Outer) (hy : y ∈ P) :
      seedHits Γ (neighborSet Γ P) y = Fintype.card Candidate := by
    have hall : Finset.univ.filter (fun z => Γ y z ∈ neighborSet Γ P) = Finset.univ := by
      apply Finset.filter_eq_self.mpr
      intro z _
      exact Finset.mem_biUnion.mpr ⟨y, hy,
        Finset.mem_image.mpr ⟨z, Finset.mem_univ _, rfl⟩⟩
    simp only [seedHits, hall, Finset.card_univ]
  have hsum : (∑ y ∈ P, (seedHits Γ (neighborSet Γ P) y : ℝ)) =
      (P.card : ℝ) * Fintype.card Candidate := by
    calc
      _ = ∑ _y ∈ P, (Fintype.card Candidate : ℝ) :=
        Finset.sum_congr rfl fun y hy => by rw [hits y hy]
      _ = _ := by simp
  have hdiscrepancy := (abs_le.mp (extract P hP (neighborSet Γ P))).2
  rw [hsum] at hdiscrepancy
  have hp : (0 : ℝ) < P.card := by exact_mod_cast positive.trans_le hP
  have hc : (0 : ℝ) < Fintype.card Candidate := by exact_mod_cast Fintype.card_pos
  apply (mul_le_mul_iff_right₀ (mul_pos hp hc)).mp
  nlinarith [hdiscrepancy]

theorem somewhereBadInputs_subset {α Outer Candidate Base Ω : Type*}
    [Fintype α] [Fintype Outer] [Fintype Candidate] [Fintype Base] [Nonempty Base]
    {Γ : Outer → Candidate → Base} {K : Nat} {ρ ε₀ ε : ℝ}
    (cover : NeighborCoverage Γ K ρ) (separate : 2 * ε₀ < ρ)
    (budget : (K : ℝ) ≤ 2 * ε * Fintype.card Outer)
    (E : α → Base → Ω) (T : Finset Ω) :
    somewhereBadInputs (fun x y z => E x (Γ y z)) T ε ⊆ badInputs E T ε₀ := by
  intro x hx
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  by_contra hn
  have hcard : ((allHitSeeds (fun x y z => E x (Γ y z)) T x).card : ℝ) < K := by
    exact_mod_cast card_allHitSeeds_lt cover separate E T x (le_of_not_gt hn)
  have hbad := (Finset.mem_filter.mp hx).2
  linarith

theorem sampler_amplify {α Outer Candidate Base Ω : Type*}
    [Fintype α] [Fintype Outer] [Fintype Candidate] [Fintype Base] [Fintype Ω]
    [Nonempty Base] {E : α → Base → Ω} {Γ : Outer → Candidate → Base}
    {K : Nat} {L ε₀ ε δ ρ : ℝ}
    (sample : Sampler E L ε₀ δ) (cover : NeighborCoverage Γ K ρ)
    (small : ε ≤ ε₀) (separate : 2 * ε₀ < ρ)
    (budget : (K : ℝ) ≤ 2 * ε * Fintype.card Outer) :
    SomewhereSampler (fun x y z => E x (Γ y z)) L ε δ := by
  intro T hT p hp hmass hcap
  have hTbase : (T.card : ℝ) ≤ ε₀ * Fintype.card Ω :=
    hT.trans (mul_le_mul_of_nonneg_right small (Nat.cast_nonneg _))
  apply le_trans ?_ (sample T hTbase p hp hmass hcap)
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (somewhereBadInputs_subset cover separate budget E T) fun x _ _ => hp x

theorem neighborCoverage_seedProjection {Outer Base : Type*} [Fintype Base]
    {K : Nat} (positive : 0 < K) :
    NeighborCoverage (fun (_ : Outer) (z : Base) => z) K 1 := by
  intro P hP
  obtain ⟨y, hy⟩ := Finset.card_pos.mp (positive.trans_le hP)
  have hall : neighborSet (fun (_ : Outer) (z : Base) => z) P = Finset.univ := by
    ext z
    constructor
    · intro _
      exact Finset.mem_univ _
    · intro _
      exact Finset.mem_biUnion.mpr ⟨y, hy,
        Finset.mem_image.mpr ⟨z, Finset.mem_univ _, rfl⟩⟩
  simp [hall]

theorem somewhereSampler_seedProjection {α Outer Ω : Type*}
    [Fintype α] [Fintype Outer] [Fintype Ω] [Nonempty Ω]
    {L ε : ℝ} (nonneg : 0 ≤ ε) (small : ε < 1) :
    SomewhereSampler (fun (_ : α) (_ : Outer) (z : Ω) => z) L ε 0 := by
  intro T hT p _ _ _
  have hout : (0 : ℝ) < Fintype.card Ω := by exact_mod_cast Fintype.card_pos
  have hnot : ¬ ∀ z : Ω, z ∈ T := by
    intro h
    have hall : T = Finset.univ := Finset.eq_univ_iff_forall.mpr h
    rw [hall, Finset.card_univ] at hT
    have hstrict := mul_lt_mul_of_pos_right small hout
    linarith
  have hits (x : α) :
      allHitSeeds (fun (_ : α) (_ : Outer) (z : Ω) => z) T x = ∅ := by
    simp [allHitSeeds, hnot]
  have hbad : somewhereBadInputs (fun (_ : α) (_ : Outer) (z : Ω) => z) T ε = ∅ := by
    ext x
    simp only [somewhereBadInputs, Finset.mem_filter, Finset.mem_univ, true_and,
      hits, Finset.card_empty, Nat.cast_zero, Finset.notMem_empty, iff_false]
    exact not_lt.mpr (mul_nonneg (mul_nonneg (by norm_num) nonneg) (Nat.cast_nonneg _))
  simp [hbad]

end Algebraic.Cutwidth.Extractor.Internal
