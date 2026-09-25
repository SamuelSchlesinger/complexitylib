/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Fusion.Arithmetic.Support
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Data.Finset.Image

/-!
# Support fusion for monotone multivariate-polynomial circuits

Natural-coefficient multivariate polynomials have exact support semantics:
support turns addition into union and multiplication into pairwise addition of
exponent vectors.  This file packages that map as an `Algebraic.Homomorphism`
from genuine arithmetic circuits over `MvPolynomial σ ℕ` to the finite-support
interpretation.

The resulting lower bound applies to arbitrary-depth monotone arithmetic
circuits whose multiplication gates have bounded input-support width.  The
width promise is evaluated in the support interpretation, equivalently on the
supports of the polynomials at the corresponding source-circuit wires.
-/

@[expose] public section

namespace Algebraic
namespace Fusion
namespace Arithmetic
namespace MonotonePolynomial

open scoped Pointwise

noncomputable section

/-- A polynomial monomial represented by its exponent vector, with
multiplication given by addition of exponents. -/
structure Monomial (σ : Type u) where
  /-- Exponent vector of the monomial. -/
  exponent : σ →₀ ℕ
  deriving DecidableEq

@[ext] theorem Monomial.ext
    {left right : Monomial σ}
    (equal : left.exponent = right.exponent) : left = right := by
  cases left
  cases right
  cases equal
  rfl

instance : Mul (Monomial σ) where
  mul left right := ⟨left.exponent + right.exponent⟩

@[simp] theorem exponent_mul (left right : Monomial σ) :
    (left * right).exponent = left.exponent + right.exponent := rfl

/-- Inject exponent vectors into the multiplicative monomial wrapper. -/
def monomialEmbedding (σ : Type u) : (σ →₀ ℕ) ↪ Monomial σ where
  toFun exponent := ⟨exponent⟩
  inj' := by
    intro left right equal
    exact congrArg Monomial.exponent equal

/-- The support of a natural-coefficient polynomial, expressed in the
multiplicative monomial wrapper. -/
def supportFinset
    (polynomial : MvPolynomial σ ℕ) : Finset (Monomial σ) :=
  polynomial.support.map (monomialEmbedding σ)

/-- A polynomial support as the reusable finite-support semantic carrier. -/
def supportValue
    (polynomial : MvPolynomial σ ℕ) : FiniteSupport (Monomial σ) :=
  ⟨supportFinset polynomial⟩

@[simp] theorem supportValue_monomials
    (polynomial : MvPolynomial σ ℕ) :
    (supportValue polynomial).monomials = supportFinset polynomial := rfl

@[simp] theorem card_supportFinset
    (polynomial : MvPolynomial σ ℕ) :
    (supportFinset polynomial).card = polynomial.support.card := by
  simp [supportFinset]

@[simp] theorem monomial_mem_supportFinset
    (exponent : σ →₀ ℕ)
    (polynomial : MvPolynomial σ ℕ) :
    (⟨exponent⟩ : Monomial σ) ∈ supportFinset polynomial ↔
      exponent ∈ polynomial.support := by
  classical
  constructor
  · intro present
    obtain ⟨other, otherPresent, equal⟩ :=
      Finset.mem_map.mp present
    have exponentEqual : other = exponent :=
      congrArg Monomial.exponent equal
    simpa [exponentEqual] using otherPresent
  · intro present
    exact Finset.mem_map.mpr ⟨exponent, present, rfl⟩

/-- Natural coefficients cannot cancel under addition, so support of a sum is
exactly the union of supports. -/
theorem polynomial_support_add
    [DecidableEq σ]
    (left right : MvPolynomial σ ℕ) :
    (left + right).support = left.support ∪ right.support := by
  ext exponent
  simp only [MvPolynomial.mem_support_iff, AddMonoidAlgebra.coeff_add, Finsupp.add_apply,
    Finset.mem_union]
  omega

/-- Natural coefficients cannot cancel and have no zero divisors, so every
pairwise sum of supported exponent vectors survives in the product. -/
theorem polynomial_support_mul
    [DecidableEq σ]
    (left right : MvPolynomial σ ℕ) :
    (left * right).support = left.support + right.support := by
  apply Finset.Subset.antisymm
  · exact MvPolynomial.support_mul left right
  · intro exponent present
    rw [Finset.mem_add] at present
    obtain ⟨leftExponent, leftPresent, rightExponent, rightPresent, rfl⟩ :=
      present
    rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_mul]
    apply Nat.ne_of_gt
    apply Finset.sum_pos'
    · intro pair _
      exact Nat.zero_le _
    · refine ⟨(leftExponent, rightExponent), ?_, ?_⟩
      · exact Finset.mem_antidiagonal.mpr rfl
      · exact Nat.mul_pos
          (Nat.pos_of_ne_zero
            (MvPolynomial.mem_support_iff.mp leftPresent))
          (Nat.pos_of_ne_zero
            (MvPolynomial.mem_support_iff.mp rightPresent))

@[simp] theorem supportValue_add
    [DecidableEq σ]
    (left right : MvPolynomial σ ℕ) :
    supportValue (left + right) = supportValue left + supportValue right := by
  apply congrArg FiniteSupport.mk
  simp [supportValue, supportFinset, polynomial_support_add, Finset.map_union]

@[simp] theorem supportValue_mul
    [DecidableEq σ]
    (left right : MvPolynomial σ ℕ) :
    supportValue (left * right) = supportValue left * supportValue right := by
  apply congrArg FiniteSupport.mk
  ext monomial
  constructor
  · intro present
    simp only [supportFinset, Finset.mem_map] at present
    obtain ⟨exponent, exponentPresent, equal⟩ := present
    rw [polynomial_support_mul, Finset.mem_add] at exponentPresent
    obtain ⟨leftExponent, leftPresent, rightExponent, rightPresent,
      exponentEqual⟩ := exponentPresent
    exact (FiniteSupport.mem_mul monomial
      (supportValue left) (supportValue right)).mpr
      ⟨⟨leftExponent⟩,
        Finset.mem_map.mpr ⟨leftExponent, leftPresent, rfl⟩,
        ⟨rightExponent⟩,
        Finset.mem_map.mpr ⟨rightExponent, rightPresent, rfl⟩,
        Monomial.ext (exponentEqual.trans
          (congrArg Monomial.exponent equal))⟩
  · intro present
    rw [Finset.mem_image₂] at present
    obtain ⟨leftMonomial, leftPresent, rightMonomial, rightPresent,
      equal⟩ := present
    simp only [supportValue, supportFinset, Finset.mem_map] at leftPresent
    simp only [supportValue, supportFinset, Finset.mem_map] at rightPresent
    obtain ⟨leftExponent, leftExponentPresent, leftEqual⟩ := leftPresent
    obtain ⟨rightExponent, rightExponentPresent, rightEqual⟩ := rightPresent
    subst leftMonomial
    subst rightMonomial
    apply Finset.mem_map.mpr
    refine ⟨leftExponent + rightExponent, ?_, ?_⟩
    · rw [polynomial_support_mul, Finset.mem_add]
      exact ⟨leftExponent, leftExponentPresent,
        rightExponent, rightExponentPresent, rfl⟩
    · apply Monomial.ext
      exact congrArg Monomial.exponent equal

/-- Support of the scalar constants used by the target support
interpretation. -/
def constantSupport
    (scalar : ℕ) : FiniteSupport (Monomial σ) :=
  supportValue (MvPolynomial.C scalar)

/-- Constant supports contain only the zero exponent vector. -/
theorem constantSupport_subset_zero
    (scalar : ℕ) :
    (constantSupport (σ := σ) scalar).monomials ⊆
      {(⟨0⟩ : Monomial σ)} := by
  intro monomial present
  rcases monomial with ⟨exponent⟩
  simp only [constantSupport, supportValue_monomials,
    monomial_mem_supportFinset] at present
  have exponentZero : exponent = 0 :=
    Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset present)
  simp [exponentZero]

/-- If the target has no constant monomial, every named natural constant is
sound for the support-fusion model. -/
theorem constantAvoid_of_zero_not_mem
    (target : MvPolynomial σ ℕ)
    (zero_not_mem : 0 ∉ target.support) :
    ∀ witness : ↥(supportFinset target), ∀ scalar,
      witness.1 ∉ (constantSupport (σ := σ) scalar).monomials := by
  intro witness scalar present
  have witnessZero : witness.1 = (⟨0⟩ : Monomial σ) :=
    Finset.mem_singleton.mp (constantSupport_subset_zero scalar present)
  have zeroPresent : (⟨0⟩ : Monomial σ) ∈ supportFinset target := by
    rw [← witnessZero]
    exact witness.2
  exact zero_not_mem (monomial_mem_supportFinset 0 target |>.mp zeroPresent)

/-- Disjoint source supports imply the witness-wise input-avoidance premise. -/
theorem inputAvoid_of_disjoint
    (inputs : Fin n → MvPolynomial σ ℕ)
    (target : MvPolynomial σ ℕ)
    (disjoint : ∀ input,
      Disjoint target.support (inputs input).support) :
    ∀ witness : ↥(supportFinset target), ∀ input,
      witness.1 ∉ (supportValue (inputs input)).monomials := by
  intro witness input present
  rcases witness with ⟨⟨exponent⟩, targetPresent⟩
  have exponentTarget : exponent ∈ target.support :=
    (monomial_mem_supportFinset exponent target).mp targetPresent
  have exponentInput : exponent ∈ (inputs input).support := by
    simpa only [supportValue_monomials, monomial_mem_supportFinset] using present
  exact Finset.disjoint_left.mp (disjoint input) exponentTarget exponentInput

/-- Exact polynomial support is a homomorphism of arithmetic
interpretations. -/
def supportHomomorphism
    (σ : Type u)
    [DecidableEq σ] :
    @Homomorphism
      (Algebraic.Arithmetic.signature ℕ)
      (MvPolynomial σ ℕ)
      (FiniteSupport (Monomial σ))
      ((Algebraic.Arithmetic.interpretation
        (MvPolynomial.C : ℕ → MvPolynomial σ ℕ)) :
          Interpretation (Algebraic.Arithmetic.signature ℕ)
            (MvPolynomial σ ℕ))
      ((Algebraic.Arithmetic.interpretation
        (constantSupport (σ := σ))) :
          Interpretation (Algebraic.Arithmetic.signature ℕ)
            (FiniteSupport (Monomial σ))) where
  map := supportValue
  homomorphic := by
    intro op arguments
    cases op with
    | add =>
        exact supportValue_add _ _
    | mul =>
        exact supportValue_mul _ _
    | constant scalar =>
        rfl

/-- The multiplication-input support-width promise for a genuine polynomial
circuit.  Its definition evaluates the same syntax in the exact support
interpretation furnished by `supportHomomorphism`. -/
abbrev MultiplicationSupportWidthAtMost
    [DecidableEq σ]
    (circuit : Circuit (Algebraic.Arithmetic.signature ℕ) n 1)
    (inputs : Fin n → MvPolynomial σ ℕ)
    (width : Nat) : Prop :=
  Support.MultiplicationWidthAtMost
    (circuitAtoms circuit
      (Algebraic.Arithmetic.interpretation
        (constantSupport (σ := σ)))
      (supportValue ∘ inputs)) width

/-- A polynomial construction maps to the corresponding exact support
construction. -/
theorem constructs_support
    [DecidableEq σ]
    (inputs : Fin n → MvPolynomial σ ℕ)
    (target : MvPolynomial σ ℕ)
    (circuit : Circuit (Algebraic.Arithmetic.signature ℕ) n 1)
    (constructs :
      ({ inputCount := n, inputs := inputs, target := target } :
        Problem (MvPolynomial σ ℕ)).Constructs circuit
          (Algebraic.Arithmetic.interpretation MvPolynomial.C)) :
    (Support.problem (supportValue ∘ inputs) (supportFinset target)).Constructs
      circuit
        (Algebraic.Arithmetic.interpretation
          (constantSupport (σ := σ))) := by
  change circuit.eval
      (Algebraic.Arithmetic.interpretation (constantSupport (σ := σ)))
      (supportValue ∘ inputs) 0 = supportValue target
  calc
    circuit.eval
        (Algebraic.Arithmetic.interpretation (constantSupport (σ := σ)))
        (supportValue ∘ inputs) 0 =
        supportValue (circuit.eval
          (Algebraic.Arithmetic.interpretation MvPolynomial.C) inputs 0) := by
      symm
      simpa [supportHomomorphism] using congrFun
        (Circuit.map_eval circuit (supportHomomorphism σ) inputs) 0
    _ = supportValue target := congrArg supportValue constructs

/-- Transfer the arbitrary-depth support-width fusion bound to a genuine
monotone arithmetic circuit over `MvPolynomial σ ℕ`. -/
theorem circuit_multiplication_lowerBound
    [DecidableEq σ]
    (inputs : Fin n → MvPolynomial σ ℕ)
    (target : MvPolynomial σ ℕ)
    (inputAvoid : ∀ witness : ↥(supportFinset target), ∀ input,
      witness.1 ∉ (supportValue (inputs input)).monomials)
    (constantAvoid : ∀ witness : ↥(supportFinset target), ∀ scalar,
      witness.1 ∉ (constantSupport (σ := σ) scalar).monomials)
    (width : Nat)
    (positive : 0 < width)
    (circuit : Circuit (Algebraic.Arithmetic.signature ℕ) n 1)
    (constructs :
      ({ inputCount := n, inputs := inputs, target := target } :
        Problem (MvPolynomial σ ℕ)).Constructs circuit
          (Algebraic.Arithmetic.interpretation MvPolynomial.C))
    (widthBound : MultiplicationSupportWidthAtMost circuit inputs width) :
    target.support.card ⌈/⌉ (width * width) ≤
      circuit.cost
        (Algebraic.Arithmetic.multiplicationCost (K := ℕ)) := by
  simpa using Support.circuit_multiplication_lowerBound
    (constantSupport (σ := σ)) (supportValue ∘ inputs)
    (supportFinset target) inputAvoid constantAvoid width positive circuit
    (constructs_support inputs target circuit constructs) widthBound

/-- Singleton support at every multiplication input forces one multiplication
per target monomial. -/
theorem circuit_multiplication_lowerBound_of_singletonWidth
    [DecidableEq σ]
    (inputs : Fin n → MvPolynomial σ ℕ)
    (target : MvPolynomial σ ℕ)
    (inputAvoid : ∀ witness : ↥(supportFinset target), ∀ input,
      witness.1 ∉ (supportValue (inputs input)).monomials)
    (constantAvoid : ∀ witness : ↥(supportFinset target), ∀ scalar,
      witness.1 ∉ (constantSupport (σ := σ) scalar).monomials)
    (circuit : Circuit (Algebraic.Arithmetic.signature ℕ) n 1)
    (constructs :
      ({ inputCount := n, inputs := inputs, target := target } :
        Problem (MvPolynomial σ ℕ)).Constructs circuit
          (Algebraic.Arithmetic.interpretation MvPolynomial.C))
    (widthBound : MultiplicationSupportWidthAtMost circuit inputs 1) :
    target.support.card ≤
      circuit.cost
        (Algebraic.Arithmetic.multiplicationCost (K := ℕ)) := by
  simpa using circuit_multiplication_lowerBound inputs target inputAvoid
    constantAvoid 1 (by decide) circuit constructs widthBound

/-- User-facing form with ordinary support-disjointness and nonconstant-target
hypotheses. -/
theorem circuit_multiplication_lowerBound_of_disjoint
    [DecidableEq σ]
    (inputs : Fin n → MvPolynomial σ ℕ)
    (target : MvPolynomial σ ℕ)
    (inputDisjoint : ∀ input,
      Disjoint target.support (inputs input).support)
    (target_nonconstant : 0 ∉ target.support)
    (width : Nat)
    (positive : 0 < width)
    (circuit : Circuit (Algebraic.Arithmetic.signature ℕ) n 1)
    (constructs :
      ({ inputCount := n, inputs := inputs, target := target } :
        Problem (MvPolynomial σ ℕ)).Constructs circuit
          (Algebraic.Arithmetic.interpretation MvPolynomial.C))
    (widthBound : MultiplicationSupportWidthAtMost circuit inputs width) :
    target.support.card ⌈/⌉ (width * width) ≤
      circuit.cost
        (Algebraic.Arithmetic.multiplicationCost (K := ℕ)) :=
  circuit_multiplication_lowerBound inputs target
    (inputAvoid_of_disjoint inputs target inputDisjoint)
    (constantAvoid_of_zero_not_mem target target_nonconstant)
    width positive circuit constructs widthBound

end
end MonotonePolynomial
end Arithmetic
end Fusion
end Algebraic
