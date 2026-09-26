/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.DescriptiveComplexity.Definable
public import Complexitylib.DescriptiveComplexity.SecondOrder.Reduction
public import Complexitylib.DescriptiveComplexity.SecondOrder.Connectives
public import Complexitylib.DescriptiveComplexity.SecondOrder.Certificate

/-!
# Existential second-order definability

`ExistSODefinable` retains a syntactic existential SO witness for a query. It is
closed under intersection, union, and universe-preserving FO reductions, includes
FO definability, and implies isomorphism invariance. Its induced languages have
verified binary certificate checkers and polynomial witness bounds. The downstream
`SecondOrder.PolynomialTime` module proves their membership in the machine class
`Complexity.NP`, the upper direction of Fagin's theorem (Fagin, 1974).

The separation of a definability witness from reduction transport follows the
organization of Senellart and Gnatenko (2026), Sections 3--4,
<https://arxiv.org/abs/2609.18261>, specialized to our existing interpretations.
-/

@[expose] public section

namespace Complexity.DescriptiveComplexity

variable {V W : Vocabulary}

/-- A query defined by an existential SO prefix followed by an FO matrix. -/
def ExistSODefinable (Q : BooleanQuery V) : Prop :=
  ∃ φ : SOSentence V, φ.IsExistSO ∧ ∀ A : FinStruct V, Q A ↔ SOSentence.Models A φ

/-- An existential SO witness is in particular a second-order witness. -/
theorem ExistSODefinable.toSODefinable {Q : BooleanQuery V} (hQ : ExistSODefinable Q) :
    SODefinable Q := by
  obtain ⟨φ, _, hφ⟩ := hQ
  exact ⟨φ, hφ⟩

/-- Existential SO definability implies invariance under isomorphism. -/
theorem ExistSODefinable.orderIndependent {Q : BooleanQuery V} (hQ : ExistSODefinable Q) :
    Q.IsOrderIndependent := hQ.toSODefinable.orderIndependent

/-- A first-order witness is an existential SO witness with an empty prefix. -/
theorem FODefinable.toExistSODefinable {Q : BooleanQuery V} (hQ : FODefinable Q) :
    ExistSODefinable Q := by
  obtain ⟨φ, hφ⟩ := hQ
  exact ⟨.ofFormula φ [], SOFormula.ofFormula_isExistSO φ [],
    fun A => (hφ A).trans (SOSentence.models_ofFormula A φ).symm⟩

/-- Existential SO queries are closed under intersection by merging their witness prefixes. -/
theorem ExistSODefinable.inter {Q₁ Q₂ : BooleanQuery V}
    (h₁ : ExistSODefinable Q₁) (h₂ : ExistSODefinable Q₂) :
    ExistSODefinable (Q₁.inter Q₂) := by
  obtain ⟨φ, hφ, hQ₁⟩ := h₁
  obtain ⟨ψ, hψ, hQ₂⟩ := h₂
  refine ⟨φ.existConj ψ, hφ.existConj hψ, fun A => ?_⟩
  simpa only [BooleanQuery.inter, hQ₁ A, hQ₂ A, SOSentence.Models] using
    (φ.existConj_sat ψ A (emptyEnv A.card) (emptyREnv A.card)).symm

/-- Existential SO queries are closed under union by merging their witness prefixes. -/
theorem ExistSODefinable.union {Q₁ Q₂ : BooleanQuery V}
    (h₁ : ExistSODefinable Q₁) (h₂ : ExistSODefinable Q₂) :
    ExistSODefinable (Q₁.union Q₂) := by
  obtain ⟨φ, hφ, hQ₁⟩ := h₁
  obtain ⟨ψ, hψ, hQ₂⟩ := h₂
  refine ⟨φ.existDisj ψ, hφ.existDisj hψ, fun A => ?_⟩
  simpa only [BooleanQuery.union, hQ₁ A, hQ₂ A, SOSentence.Models] using
    (φ.existDisj_sat ψ A (emptyEnv A.card) (emptyREnv A.card)).symm

/-- An existential SO query has an exact binary verifier with polynomially bounded certificates. -/
theorem ExistSODefinable.exists_bounded_certificate {Q : BooleanQuery V}
    (hQ : ExistSODefinable Q) :
    ∃ (φ : SOSentence V) (h : φ.IsExistSO), ∀ input : List Bool,
      input ∈ queryLanguage Q ↔
        ∃ certificate, certificate.length ≤ φ.witnessPolynomial.eval input.length ∧
          φ.checkEncoded h input certificate = true := by
  obtain ⟨φ, h, hφ⟩ := hQ
  refine ⟨φ, h, fun input => ?_⟩
  rw [SOSentence.exists_checkEncoded_bounded_iff]
  simp only [mem_queryLanguage_iff_decodeStruct, hφ]

/-- Existential SO definability travels backward through FO reductions. -/
theorem ExistSODefinable.of_reduces {Q₁ : BooleanQuery V} {Q₂ : BooleanQuery W}
    (hQ₂ : ExistSODefinable Q₂) (hred : FOReduces Q₁ Q₂) : ExistSODefinable Q₁ := by
  obtain ⟨I, hI⟩ := hred
  obtain ⟨φ, hfragment, hφ⟩ := hQ₂
  exact ⟨I.translateSO φ, (I.isExistSO_translateSO φ).mpr hfragment,
    fun A => (hI A).trans ((hφ (I.apply A)).trans (I.translateSO_sat A φ _ _))⟩

/-- Existential SO definability also travels backward through quantifier-free reductions. -/
theorem ExistSODefinable.of_projReduces {Q₁ : BooleanQuery V} {Q₂ : BooleanQuery W}
    (hQ₂ : ExistSODefinable Q₂) (hred : FOProjReduces Q₁ Q₂) : ExistSODefinable Q₁ :=
  hQ₂.of_reduces hred.toFOReduces

/-- An inexpressibility result rules out every FO reduction to an existential SO query. -/
theorem not_foReduces_of_not_existSODefinable {Q₁ : BooleanQuery V} {Q₂ : BooleanQuery W}
    (hQ₁ : ¬ ExistSODefinable Q₁) (hQ₂ : ExistSODefinable Q₂) : ¬ FOReduces Q₁ Q₂ :=
  fun h => hQ₁ (hQ₂.of_reduces h)

end Complexity.DescriptiveComplexity
