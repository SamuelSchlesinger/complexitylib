/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Fusion.SumOfTerms.Rank

/-!
# Term-dependent weighted rank certificates

The ordinary sum-of-terms rank certificate uses one uniform rank bound and
counts dictionary terms.  This module allows each dictionary term to carry
its own natural weight.  If the feature rank of a term is at most that weight,
then target rank lower-bounds the circuit's exact term-dependent cost.

This is the appropriate interface for supported matrix blocks, rectangles of
different side lengths, and heterogeneous tensor pieces.
-/

@[expose] public section

namespace Algebraic
namespace Fusion
namespace SumOfTerms
namespace WeightedRank

noncomputable section

open Cardinal

variable {K : Type u} {V : Type v} {T : Type w}
variable {A : Type x} {B : Type y}
variable [Field K]
variable [AddCommGroup V] [Module K V]
variable [AddCommGroup A] [Module K A]
variable [AddCommGroup B] [Module K B]

/-- Rank certificate with a term-specific natural rank budget. -/
structure Certificate
    (termValue : T → V)
    (termWeight : T → Nat)
    (problem : Problem V) where
  /-- Linear feature whose rank measures the target. -/
  feature : V →ₗ[K] (A →ₗ[K] B)
  /-- Natural lower bound on target feature rank. -/
  targetRank : Nat
  /-- Free inputs contribute no feature rank. -/
  input_zero : ∀ input, feature (problem.inputs input) = 0
  /-- Every dictionary term fits within its own charged weight. -/
  term_rank_le : ∀ term,
    LinearMap.rank (feature (termValue term)) ≤ termWeight term
  /-- The target realizes the claimed rank. -/
  target_rank_ge : (targetRank : Cardinal) ≤
    LinearMap.rank (feature problem.target)

/-- The target feature is spanned by the features of dictionary-term
occurrences in any Fusion cover. -/
theorem Certificate.targetFeature_mem_termSpan
    {termValue : T → V}
    {termWeight : T → Nat}
    {problem : Problem V}
    (certificate : Certificate (K := K) (A := A) (B := B)
      termValue termWeight problem)
    (cover : Cover (spanModel (K := K) termValue problem)) :
    certificate.feature problem.target ∈
      Submodule.span K
        (Set.range fun index : Fin (terms cover.atoms).length ↦
          certificate.feature
            (termValue ((terms cover.atoms).get index))) := by
  let termFeature : Fin (terms cover.atoms).length → (A →ₗ[K] B) :=
    fun index ↦ certificate.feature
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
  exact generated_le_comap
    (target_mem_generatedSubmodule (K := K) termValue problem cover)

/-- Target feature rank is at most the sum of the weights of dictionary-term
occurrences in a cover. -/
theorem Certificate.target_rank_le_termWeights
    {termValue : T → V}
    {termWeight : T → Nat}
    {problem : Problem V}
    (certificate : Certificate (K := K) (A := A) (B := B)
      termValue termWeight problem)
    (cover : Cover (spanModel (K := K) termValue problem)) :
    LinearMap.rank (certificate.feature problem.target) ≤
      ∑ index : Fin (terms cover.atoms).length,
        (termWeight ((terms cover.atoms).get index) : Cardinal) := by
  classical
  let termFeature : Fin (terms cover.atoms).length → (A →ₗ[K] B) :=
    fun index ↦ certificate.feature
      (termValue ((terms cover.atoms).get index))
  have targetMem : certificate.feature problem.target ∈
      Submodule.span K (Set.range termFeature) :=
    certificate.targetFeature_mem_termSpan cover
  exact LinearMap.rank_le_sum_of_mem_span
    (certificate.feature problem.target) termFeature
    (fun index => termWeight ((terms cover.atoms).get index)) targetMem
    (fun index => certificate.term_rank_le ((terms cover.atoms).get index))

/-- Natural-number weighted cover inequality. -/
theorem Certificate.targetRank_le_termWeights
    {termValue : T → V}
    {termWeight : T → Nat}
    {problem : Problem V}
    (certificate : Certificate (K := K) (A := A) (B := B)
      termValue termWeight problem)
    (cover : Cover (spanModel (K := K) termValue problem)) :
    certificate.targetRank ≤
      ((terms cover.atoms).map termWeight).sum := by
  have cardinalBound : (certificate.targetRank : Cardinal) ≤
      ∑ index : Fin (terms cover.atoms).length,
        (termWeight ((terms cover.atoms).get index) : Cardinal) :=
    certificate.target_rank_ge.trans
      (certificate.target_rank_le_termWeights cover)
  have naturalBound : certificate.targetRank ≤
      ∑ index : Fin (terms cover.atoms).length,
        termWeight ((terms cover.atoms).get index) := by
    exact_mod_cast cardinalBound
  simpa [List.sum_ofFn] using naturalBound

/-- A weighted rank certificate lower-bounds exact term-dependent circuit
cost. -/
theorem Certificate.circuit_lowerBound
    {termValue : T → V}
    {termWeight : T → Nat}
    {problem : Problem V}
    (certificate : Certificate (K := K) (A := A) (B := B)
      termValue termWeight problem)
    (circuit : Circuit (Algebraic.SumOfTerms.signature T)
      problem.inputCount 1)
    (constructs : problem.Constructs circuit
      (Algebraic.SumOfTerms.interpretation termValue)) :
    certificate.targetRank ≤
      circuit.cost (Algebraic.SumOfTerms.dictionaryCost termWeight) := by
  let cover := coverOfCircuit (spanModel (K := K) termValue problem)
    circuit constructs
  calc
    certificate.targetRank ≤
        ((terms cover.atoms).map termWeight).sum :=
      certificate.targetRank_le_termWeights cover
    _ = Atom.listCost cover.atoms
        (Algebraic.SumOfTerms.dictionaryCost termWeight) :=
      terms_weight_sum cover.atoms termWeight
    _ = circuit.cost
        (Algebraic.SumOfTerms.dictionaryCost termWeight) := by
      exact circuitAtoms_cost circuit
        (Algebraic.SumOfTerms.interpretation termValue) problem.inputs
        (Algebraic.SumOfTerms.dictionaryCost termWeight)

end
end WeightedRank
end SumOfTerms
end Fusion
end Algebraic
