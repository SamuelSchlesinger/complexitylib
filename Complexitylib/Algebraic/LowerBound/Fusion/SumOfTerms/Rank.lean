/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Fusion.SumOfTerms
public import Mathlib.Algebra.Order.Floor.Div
public import Complexitylib.Algebraic.LinearAlgebra.Rank

/-!
# Rank certificates for sum-of-terms circuits

A catalecticant, partial-derivative matrix, tensor flattening, or evaluation
matrix is a linear map from semantic values to linear maps.  Rank is
subadditive, so if every allowed term has rank at most `r` and the target has
rank at least `R`, at least `ceil(R / r)` term gates are necessary.

This file proves that statement once for the fusion span model.  Applications
only supply the feature map and the two local rank estimates.
-/

@[expose] public section

namespace Algebraic
namespace Fusion
namespace SumOfTerms

open Cardinal

variable {K : Type u} {V : Type v} {T : Type w}
variable {A : Type x} {B : Type y}
variable [Field K]
variable [AddCommGroup V] [Module K V]
variable [AddCommGroup A] [Module K A]
variable [AddCommGroup B] [Module K B]

/-- A linear-map rank certificate for one sum-of-terms problem. -/
structure RankCertificate
    (termValue : T → V)
    (problem : Problem V) where
  /-- Linear feature whose rank measures the target. -/
  feature : V →ₗ[K] (A →ₗ[K] B)
  /-- Natural lower bound on the feature rank of the target. -/
  targetRank : Nat
  /-- Natural upper bound on the feature rank of each dictionary term. -/
  termRank : Nat
  /-- Free inputs contribute no feature rank. -/
  input_zero : ∀ input, feature (problem.inputs input) = 0
  /-- Every permitted dictionary term has bounded feature rank. -/
  term_rank_le : ∀ term,
    LinearMap.rank (feature (termValue term)) ≤ termRank
  /-- The target realizes the claimed rank. -/
  target_rank_ge : (targetRank : Cardinal) ≤
    LinearMap.rank (feature problem.target)

/-- The feature of the target lies in the span of the features of the term
atoms in a cover. -/
theorem RankCertificate.targetFeature_mem_termSpan
    {termValue : T → V}
    {problem : Problem V}
    (certificate : RankCertificate (K := K) (A := A) (B := B) termValue problem)
    (cover : Cover (spanModel (K := K) termValue problem)) :
    certificate.feature problem.target ∈
      Submodule.span K
        (Set.range fun index : Fin (terms cover.atoms).length =>
          certificate.feature
            (termValue ((terms cover.atoms).get index))) := by
  let termFeature : Fin (terms cover.atoms).length → (A →ₗ[K] B) :=
    fun index => certificate.feature
      (termValue ((terms cover.atoms).get index))
  let targetSpan : Submodule K (A →ₗ[K] B) :=
    Submodule.span K (Set.range termFeature)
  have generated_le_comap :
      generatedSubmodule (K := K) termValue problem cover.atoms ≤
        Submodule.comap certificate.feature targetSpan := by
    apply Submodule.span_le.2
    intro value present
    rcases present with inputPresent | termPresent
    · obtain ⟨input, rfl⟩ := inputPresent
      change certificate.feature (problem.inputs input) ∈ targetSpan
      rw [certificate.input_zero input]
      exact targetSpan.zero_mem
    · obtain ⟨index, rfl⟩ := termPresent
      change termFeature index ∈ targetSpan
      exact Submodule.subset_span ⟨index, rfl⟩
  have targetMem := target_mem_generatedSubmodule
    (K := K) termValue problem cover
  exact generated_le_comap targetMem

/-- Compatibility name for `LinearMap.rank_smul_le`. -/
@[deprecated LinearMap.rank_smul_le (since := "2026-09-15")]
alias linearMap_rank_smul_le := LinearMap.rank_smul_le

/-- The feature rank of the target is at most the number of terms times their
individual rank bound. -/
theorem RankCertificate.target_rank_le_terms
    {termValue : T → V}
    {problem : Problem V}
    (certificate : RankCertificate (K := K) (A := A) (B := B) termValue problem)
    (cover : Cover (spanModel (K := K) termValue problem)) :
    LinearMap.rank (certificate.feature problem.target) ≤
      ((terms cover.atoms).length : Cardinal) * certificate.termRank := by
  classical
  let termFeature : Fin (terms cover.atoms).length → (A →ₗ[K] B) :=
    fun index => certificate.feature
      (termValue ((terms cover.atoms).get index))
  have targetMem : certificate.feature problem.target ∈
      Submodule.span K (Set.range termFeature) :=
    certificate.targetFeature_mem_termSpan cover
  have bound := LinearMap.rank_le_sum_of_mem_span
    (certificate.feature problem.target) termFeature (fun _ => certificate.termRank)
    targetMem (fun index => certificate.term_rank_le ((terms cover.atoms).get index))
  simpa [nsmul_eq_mul] using bound

/-- A rank certificate gives the natural-number cover inequality
`targetRank ≤ cost * termRank`. -/
theorem RankCertificate.targetRank_le_mul_coverCost
    {termValue : T → V}
    {problem : Problem V}
    (certificate : RankCertificate (K := K) (A := A) (B := B) termValue problem)
    (cover : Cover (spanModel (K := K) termValue problem)) :
    certificate.targetRank ≤ cover.cost * certificate.termRank := by
  have cardinalBound : (certificate.targetRank : Cardinal) ≤
      ((terms cover.atoms).length : Cardinal) * certificate.termRank :=
    certificate.target_rank_ge.trans
      (certificate.target_rank_le_terms cover)
  have naturalBound : certificate.targetRank ≤
      (terms cover.atoms).length * certificate.termRank := by
    exact_mod_cast cardinalBound
  change certificate.targetRank ≤
    Atom.listCost cover.atoms (Algebraic.SumOfTerms.termCost (T := T)) *
      certificate.termRank
  rw [← terms_length]
  exact naturalBound

/-- Dividing by a positive per-term rank gives a cover-cost lower bound. -/
theorem RankCertificate.ceilDiv_targetRank_le_coverCost
    {termValue : T → V}
    {problem : Problem V}
    (certificate : RankCertificate (K := K) (A := A) (B := B) termValue problem)
    (positive : 0 < certificate.termRank)
    (cover : Cover (spanModel (K := K) termValue problem)) :
    certificate.targetRank ⌈/⌉ certificate.termRank ≤ cover.cost :=
  (ceilDiv_le_iff_le_mul positive).2
    (by simpa [Nat.mul_comm] using
      certificate.targetRank_le_mul_coverCost cover)

/-- Rank/partial-derivative lower bound transferred to sum-of-terms circuits. -/
theorem RankCertificate.circuit_lowerBound
    {termValue : T → V}
    {problem : Problem V}
    (certificate : RankCertificate (K := K) (A := A) (B := B) termValue problem)
    (positive : 0 < certificate.termRank)
    (circuit : Circuit (Algebraic.SumOfTerms.signature T)
      problem.inputCount g 1)
    (constructs : problem.Constructs circuit
      (Algebraic.SumOfTerms.interpretation termValue)) :
    certificate.targetRank ⌈/⌉ certificate.termRank ≤
      circuit.cost (Algebraic.SumOfTerms.termCost (T := T)) :=
  (spanModel (K := K) termValue problem).lowerBound
    (certificate.ceilDiv_targetRank_le_coverCost positive)
    circuit constructs

end SumOfTerms
end Fusion
end Algebraic
