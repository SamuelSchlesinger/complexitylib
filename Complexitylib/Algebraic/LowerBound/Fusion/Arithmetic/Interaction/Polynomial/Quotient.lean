/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Fusion.Arithmetic.Interaction.Linear.Quotient
public import Complexitylib.Algebraic.LowerBound.Fusion.Arithmetic.Interaction.Polynomial

/-!
# Polynomial coordinates on the canonical nonlinear quotient

Selected nonconstant, non-input coefficients vanish on the polynomial
free-data submodule, so the coefficient feature factors through the canonical
quotient by inputs and named constants.  The rank of a selected coefficient
matrix is therefore bounded by the coordinate-free quotient-output rank.

This identifies coefficient arguments as explicit coordinate witnesses for
the canonical quotient obstruction rather than a separate lower-bound method.
-/

@[expose] public section

namespace Algebraic
namespace Fusion
namespace Arithmetic
namespace Interaction
namespace Polynomial
namespace Quotient

noncomputable section

variable {K : Type u} {C : Type v} {σ : Type w} {I : Type x}

/-- Selected coefficients, descended to the quotient by free inputs and named
constants. -/
def coefficientFeatureOnQuotient
    [Field K]
    [DecidableEq σ]
    (constant : C → K)
    (inputVariables : Fin n → σ)
    (exponent : I → σ →₀ ℕ)
    (nonconstant : ∀ selected, exponent selected ≠ 0)
    (notInput : ∀ selected input,
      exponent selected ≠ Finsupp.single (inputVariables input) 1) :
    (MvPolynomial σ K ⧸
      Linear.Quotient.freeSubmodule K
        (fun scalar => MvPolynomial.C (constant scalar))
        (inputProblem inputVariables)) →ₗ[K] (I → K) := by
  let free := Linear.Quotient.freeSubmodule K
    (fun scalar => MvPolynomial.C (constant scalar))
    (inputProblem inputVariables)
  exact free.liftQ (coefficientFeature exponent) (by
    dsimp [free, Linear.Quotient.freeSubmodule]
    rw [Submodule.span_le]
    intro polynomial present
    change coefficientFeature exponent polynomial = 0
    rcases present with inputPresent | constantPresent
    · obtain ⟨input, rfl⟩ := inputPresent
      exact coefficientFeature_X_eq_zero exponent (inputVariables input)
        (fun selected => notInput selected input)
    · obtain ⟨scalar, rfl⟩ := constantPresent
      exact coefficientFeature_C_eq_zero exponent nonconstant
        (constant scalar))

/-- Descending to the quotient and then taking selected coefficients agrees
with taking selected coefficients directly. -/
theorem coefficientFeatureOnQuotient_mkQ
    [Field K]
    [DecidableEq σ]
    (constant : C → K)
    (inputVariables : Fin n → σ)
    (exponent : I → σ →₀ ℕ)
    (nonconstant : ∀ selected, exponent selected ≠ 0)
    (notInput : ∀ selected input,
      exponent selected ≠ Finsupp.single (inputVariables input) 1)
    (polynomial : MvPolynomial σ K) :
    coefficientFeatureOnQuotient constant inputVariables exponent
        nonconstant notInput
        ((Linear.Quotient.freeSubmodule K
          (fun scalar => MvPolynomial.C (constant scalar))
          (inputProblem inputVariables)).mkQ polynomial) =
      coefficientFeature exponent polynomial := by
  rfl

/-- Selected coefficient-matrix rank cannot exceed the canonical output rank
modulo free inputs and named constants. -/
theorem coefficientMatrix_rank_le_outputRank
    [Field K]
    [DecidableEq σ]
    (constant : C → K)
    (inputVariables : Fin n → σ)
    (exponent : I → σ →₀ ℕ)
    (nonconstant : ∀ selected, exponent selected ≠ 0)
    (notInput : ∀ selected input,
      exponent selected ≠ Finsupp.single (inputVariables input) 1)
    (outputs : Fin m → MvPolynomial σ K) :
    (coefficientMatrix exponent outputs).rank ≤
      Linear.Quotient.outputRank (K := K)
        (fun scalar => MvPolynomial.C (constant scalar))
        (inputProblem inputVariables) outputs := by
  let free := Linear.Quotient.freeSubmodule K
    (fun scalar => MvPolynomial.C (constant scalar))
    (inputProblem inputVariables)
  let quotientFeatures : Fin m →
      (MvPolynomial σ K ⧸ free) :=
    free.mkQ ∘ outputs
  let quotientSpan := Submodule.span K (Set.range quotientFeatures)
  let descended := coefficientFeatureOnQuotient constant inputVariables
    exponent nonconstant notInput
  have factor : descended ∘ quotientFeatures =
      coefficientFeature exponent ∘ outputs := by
    funext output
    exact coefficientFeatureOnQuotient_mkQ constant inputVariables exponent
      nonconstant notInput (outputs output)
  have map_eq : quotientSpan.map descended =
      Submodule.span K
        (Set.range (coefficientFeature exponent ∘ outputs)) := by
    rw [Submodule.map_span, ← Set.range_comp, factor]
  let _ : Module.Finite K quotientSpan := by
    exact Module.Finite.span_of_finite K (Set.finite_range quotientFeatures)
  calc
    (coefficientMatrix exponent outputs).rank =
        Module.finrank K
          (Submodule.span K
            (Set.range (coefficientFeature exponent ∘ outputs))) := by
      rw [Matrix.rank_eq_finrank_span_cols]
      congr 2
    _ = Module.finrank K (quotientSpan.map descended) := by
      rw [map_eq]
    _ ≤ Module.finrank K quotientSpan :=
      Submodule.finrank_map_le descended quotientSpan
    _ = Linear.Quotient.outputRank (K := K)
        (fun scalar => MvPolynomial.C (constant scalar))
        (inputProblem inputVariables) outputs :=
      rfl

/-- If the selected coefficient feature has exactly the free-data submodule
as its kernel, then its matrix rank equals the canonical quotient-output rank. -/
theorem coefficientMatrix_rank_eq_outputRank_of_ker_eq
    [Field K]
    [DecidableEq σ]
    (constant : C → K)
    (inputVariables : Fin n → σ)
    (exponent : I → σ →₀ ℕ)
    (nonconstant : ∀ selected, exponent selected ≠ 0)
    (notInput : ∀ selected input,
      exponent selected ≠ Finsupp.single (inputVariables input) 1)
    (kernel_eq : LinearMap.ker (coefficientFeature exponent) =
      Linear.Quotient.freeSubmodule K
        (fun scalar => MvPolynomial.C (constant scalar))
        (inputProblem inputVariables))
    (outputs : Fin m → MvPolynomial σ K) :
    (coefficientMatrix exponent outputs).rank =
      Linear.Quotient.outputRank (K := K)
        (fun scalar => MvPolynomial.C (constant scalar))
        (inputProblem inputVariables) outputs := by
  let free := Linear.Quotient.freeSubmodule K
    (fun scalar => MvPolynomial.C (constant scalar))
    (inputProblem inputVariables)
  let quotientFeatures : Fin m →
      (MvPolynomial σ K ⧸ free) :=
    free.mkQ ∘ outputs
  let quotientSpan := Submodule.span K (Set.range quotientFeatures)
  let descended := coefficientFeatureOnQuotient constant inputVariables
    exponent nonconstant notInput
  have factor : descended ∘ quotientFeatures =
      coefficientFeature exponent ∘ outputs := by
    funext output
    exact coefficientFeatureOnQuotient_mkQ constant inputVariables exponent
      nonconstant notInput (outputs output)
  have map_eq : quotientSpan.map descended =
      Submodule.span K
        (Set.range (coefficientFeature exponent ∘ outputs)) := by
    rw [Submodule.map_span, ← Set.range_comp, factor]
  have descended_ker : LinearMap.ker descended = ⊥ := by
    dsimp [descended]
    unfold coefficientFeatureOnQuotient
    apply Submodule.ker_liftQ_eq_bot'
    exact kernel_eq.symm
  have descended_injective : Function.Injective descended :=
    LinearMap.ker_eq_bot.mp descended_ker
  have map_finrank_eq : Module.finrank K quotientSpan =
      Module.finrank K (quotientSpan.map descended) :=
    (Submodule.equivMapOfInjective descended descended_injective
      quotientSpan).finrank_eq
  calc
    (coefficientMatrix exponent outputs).rank =
        Module.finrank K
          (Submodule.span K
            (Set.range (coefficientFeature exponent ∘ outputs))) := by
      rw [Matrix.rank_eq_finrank_span_cols]
      congr 2
    _ = Module.finrank K (quotientSpan.map descended) := by
      rw [map_eq]
    _ = Module.finrank K quotientSpan := map_finrank_eq.symm
    _ = Linear.Quotient.outputRank (K := K)
        (fun scalar => MvPolynomial.C (constant scalar))
        (inputProblem inputVariables) outputs :=
      rfl

/-- The coordinate comparison and canonical quotient theorem recover the
selected coefficient-matrix multiplication lower bound. -/
theorem coefficientMatrix_rank_le_multiplicationCost_viaQuotient
    [Field K]
    [DecidableEq σ]
    (constant : C → K)
    (inputVariables : Fin n → σ)
    (exponent : I → σ →₀ ℕ)
    (nonconstant : ∀ selected, exponent selected ≠ 0)
    (notInput : ∀ selected input,
      exponent selected ≠ Finsupp.single (inputVariables input) 1)
    (outputs : Fin m → MvPolynomial σ K)
    (circuit : Circuit (Algebraic.Arithmetic.signature C) n g m)
    (constructs : Multiple.Constructs
      (constant := fun scalar => MvPolynomial.C (constant scalar))
      (inputProblem inputVariables) outputs circuit) :
    (coefficientMatrix exponent outputs).rank ≤
      circuit.cost
        (Algebraic.Arithmetic.multiplicationCost (K := C)) :=
  (coefficientMatrix_rank_le_outputRank constant inputVariables exponent
    nonconstant notInput outputs).trans
      (Linear.Quotient.outputRank_le_multiplicationCost (K := K)
        (fun scalar => MvPolynomial.C (constant scalar))
        (inputProblem inputVariables) outputs circuit constructs)

end
end Quotient
end Polynomial
end Interaction
end Arithmetic
end Fusion
end Algebraic
