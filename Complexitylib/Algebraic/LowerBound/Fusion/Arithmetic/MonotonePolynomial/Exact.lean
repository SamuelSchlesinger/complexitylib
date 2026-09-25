/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Fusion.Arithmetic.ExactSupport
public import Complexitylib.Algebraic.LowerBound.Fusion.Arithmetic.MonotonePolynomial

/-!
# Support-width multiplication bounds over exact-support semirings

This module generalizes the natural-coefficient polynomial bridge for finite-
support Fusion.  Over any nontrivial zero-sum-free commutative semiring without
zero divisors, polynomial support maps addition to union and multiplication to
pairwise exponent addition.  The map is therefore a homomorphism into the
existing finite-support arithmetic interpretation.

Consequently the arbitrary-depth multiplication lower bound applies to
polynomial circuits over any exact-support coefficient semiring and any named
constant alphabet.  The only circuit-local promise remains the actual support
width at multiplication inputs.
-/

@[expose] public section

namespace Algebraic
namespace Fusion
namespace Arithmetic
namespace MonotonePolynomial
namespace Exact

noncomputable section

open scoped Pointwise

section SupportMap

variable [CommSemiring R]

/-- Exponent support embedded into the multiplicative monomial carrier. -/
def supportFinset
    (polynomial : MvPolynomial σ R) :
    Finset (Monomial σ) :=
  polynomial.support.map (monomialEmbedding σ)

/-- Polynomial support as the reusable finite-support semantic value. -/
def supportValue
    (polynomial : MvPolynomial σ R) :
    FiniteSupport (Monomial σ) :=
  ⟨supportFinset polynomial⟩

@[simp] theorem supportValue_monomials
    (polynomial : MvPolynomial σ R) :
    (supportValue polynomial).monomials = supportFinset polynomial := rfl

@[simp] theorem card_supportFinset
    (polynomial : MvPolynomial σ R) :
    (supportFinset polynomial).card = polynomial.support.card := by
  simp [supportFinset]

@[simp] theorem monomial_mem_supportFinset
    (exponent : σ →₀ ℕ)
    (polynomial : MvPolynomial σ R) :
    (⟨exponent⟩ : Monomial σ) ∈ supportFinset polynomial ↔
      exponent ∈ polynomial.support := by
  classical
  constructor
  · intro present
    obtain ⟨other, otherPresent, equal⟩ := Finset.mem_map.mp present
    have exponentEqual : other = exponent :=
      congrArg Monomial.exponent equal
    simpa [exponentEqual] using otherPresent
  · intro present
    exact Finset.mem_map.mpr ⟨exponent, present, rfl⟩

end SupportMap

section Homomorphism

variable [CommSemiring R] [Nontrivial R]
variable [NoZeroDivisors R] [ExactSupport.ZeroSumFree R]

omit [Nontrivial R] [NoZeroDivisors R] in
/-- Exact support respects polynomial addition. -/
@[simp] theorem supportValue_add
    [DecidableEq σ]
    (left right : MvPolynomial σ R) :
    supportValue (left + right) =
      supportValue left + supportValue right := by
  apply congrArg FiniteSupport.mk
  simp [supportValue, supportFinset,
    ExactSupport.polynomial_support_add, Finset.map_union]

omit [Nontrivial R] in
/-- Exact support respects polynomial multiplication. -/
@[simp] theorem supportValue_mul
    [DecidableEq σ]
    (left right : MvPolynomial σ R) :
    supportValue (left * right) =
      supportValue left * supportValue right := by
  apply congrArg FiniteSupport.mk
  ext monomial
  constructor
  · intro present
    simp only [supportFinset, Finset.mem_map] at present
    obtain ⟨exponent, exponentPresent, equal⟩ := present
    rw [ExactSupport.polynomial_support_mul,
      Finset.mem_add] at exponentPresent
    obtain ⟨leftExponent, leftPresent,
      rightExponent, rightPresent, exponentEqual⟩ := exponentPresent
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
    obtain ⟨leftMonomial, leftPresent,
      rightMonomial, rightPresent, equal⟩ := present
    simp only [supportValue, supportFinset,
      Finset.mem_map] at leftPresent
    simp only [supportValue, supportFinset,
      Finset.mem_map] at rightPresent
    obtain ⟨leftExponent, leftExponentPresent, leftEqual⟩ := leftPresent
    obtain ⟨rightExponent, rightExponentPresent, rightEqual⟩ := rightPresent
    subst leftMonomial
    subst rightMonomial
    apply Finset.mem_map.mpr
    refine ⟨leftExponent + rightExponent, ?_, ?_⟩
    · rw [ExactSupport.polynomial_support_mul, Finset.mem_add]
      exact ⟨leftExponent, leftExponentPresent,
        rightExponent, rightExponentPresent, rfl⟩
    · apply Monomial.ext
      exact congrArg Monomial.exponent equal

/-- Support of a scalar constant. -/
def constantSupport
    (scalar : R) : FiniteSupport (Monomial σ) :=
  supportValue (MvPolynomial.C scalar)

omit [Nontrivial R] [NoZeroDivisors R]
    [ExactSupport.ZeroSumFree R] in
/-- Every scalar constant support is contained in the zero exponent. -/
theorem constantSupport_subset_zero
    (scalar : R) :
    (constantSupport (σ := σ) scalar).monomials ⊆
      {(⟨0⟩ : Monomial σ)} := by
  intro monomial present
  rcases monomial with ⟨exponent⟩
  simp only [constantSupport, supportValue_monomials,
    monomial_mem_supportFinset] at present
  have exponentZero : exponent = 0 :=
    Finset.mem_singleton.mp
      (MvPolynomial.support_monomial_subset present)
  simp [exponentZero]

/-- Exact support is a homomorphism of the two arithmetic
interpretations. -/
def supportHomomorphism
    (σ : Type u)
    [DecidableEq σ]
    (constant : K → R) :
    @Homomorphism
      (Algebraic.Arithmetic.signature K)
      (MvPolynomial σ R)
      (FiniteSupport (Monomial σ))
      ((Algebraic.Arithmetic.interpretation
        (fun scalar => MvPolynomial.C (constant scalar))) :
          Interpretation (Algebraic.Arithmetic.signature K)
            (MvPolynomial σ R))
      ((Algebraic.Arithmetic.interpretation
        (fun scalar => constantSupport (σ := σ) (constant scalar))) :
          Interpretation (Algebraic.Arithmetic.signature K)
            (FiniteSupport (Monomial σ))) where
  map := supportValue
  homomorphic := by
    intro op arguments
    cases op with
    | add => exact supportValue_add _ _
    | mul => exact supportValue_mul _ _
    | constant scalar => rfl

end Homomorphism

section Avoidance

variable [CommSemiring R] [Nontrivial R]
variable [NoZeroDivisors R] [ExactSupport.ZeroSumFree R]

omit [Nontrivial R] [NoZeroDivisors R]
    [ExactSupport.ZeroSumFree R] in
/-- If the target has no constant monomial, every scalar constant avoids all
target witnesses. -/
theorem constantAvoid_of_zero_not_mem
    (constant : K → R)
    (target : MvPolynomial σ R)
    (zero_not_mem : 0 ∉ target.support) :
    ∀ witness : ↥(supportFinset target), ∀ scalar,
      witness.1 ∉
        (constantSupport (σ := σ) (constant scalar)).monomials := by
  intro witness scalar present
  have witnessZero : witness.1 = (⟨0⟩ : Monomial σ) :=
    Finset.mem_singleton.mp
      (constantSupport_subset_zero (constant scalar) present)
  have zeroPresent : (⟨0⟩ : Monomial σ) ∈ supportFinset target := by
    rw [← witnessZero]
    exact witness.2
  exact zero_not_mem
    (monomial_mem_supportFinset 0 target |>.mp zeroPresent)

omit [Nontrivial R] [NoZeroDivisors R]
    [ExactSupport.ZeroSumFree R] in
/-- Disjoint input and target supports imply witness-wise input avoidance. -/
theorem inputAvoid_of_disjoint
    (inputs : Fin n → MvPolynomial σ R)
    (target : MvPolynomial σ R)
    (disjoint : ∀ input,
      Disjoint target.support (inputs input).support) :
    ∀ witness : ↥(supportFinset target), ∀ input,
      witness.1 ∉ (supportValue (inputs input)).monomials := by
  intro witness input present
  rcases witness with ⟨⟨exponent⟩, targetPresent⟩
  have exponentTarget : exponent ∈ target.support :=
    (monomial_mem_supportFinset exponent target).mp targetPresent
  have exponentInput : exponent ∈ (inputs input).support := by
    simpa only [supportValue_monomials,
      monomial_mem_supportFinset] using present
  exact Finset.disjoint_left.mp (disjoint input)
    exponentTarget exponentInput

end Avoidance

section Circuit

variable [CommSemiring R] [Nontrivial R]
variable [NoZeroDivisors R] [ExactSupport.ZeroSumFree R]

/-- Multiplication-input support-width promise for a polynomial circuit. -/
abbrev MultiplicationSupportWidthAtMost
    [DecidableEq σ]
    (constant : K → R)
    (circuit : Circuit (Algebraic.Arithmetic.signature K) n 1)
    (inputs : Fin n → MvPolynomial σ R)
    (width : Nat) : Prop :=
  Support.MultiplicationWidthAtMost
    (circuitAtoms circuit
      (Algebraic.Arithmetic.interpretation
        (fun scalar => constantSupport (σ := σ) (constant scalar)))
      (supportValue ∘ inputs)) width

omit [Nontrivial R] in
/-- Polynomial construction maps to exact support construction. -/
theorem constructs_support
    [DecidableEq σ]
    (constant : K → R)
    (inputs : Fin n → MvPolynomial σ R)
    (target : MvPolynomial σ R)
    (circuit : Circuit (Algebraic.Arithmetic.signature K) n 1)
    (constructs :
      ({ inputCount := n, inputs := inputs, target := target } :
        Problem (MvPolynomial σ R)).Constructs circuit
          (Algebraic.Arithmetic.interpretation
            (fun scalar => MvPolynomial.C (constant scalar)))) :
    (Support.problem (supportValue ∘ inputs)
      (supportFinset target)).Constructs circuit
        (Algebraic.Arithmetic.interpretation
          (fun scalar => constantSupport (σ := σ) (constant scalar))) := by
  change circuit.eval
      (Algebraic.Arithmetic.interpretation
        (fun scalar => constantSupport (σ := σ) (constant scalar)))
      (supportValue ∘ inputs) 0 = supportValue target
  calc
    circuit.eval
        (Algebraic.Arithmetic.interpretation
          (fun scalar => constantSupport (σ := σ) (constant scalar)))
        (supportValue ∘ inputs) 0 =
        supportValue (circuit.eval
          (Algebraic.Arithmetic.interpretation
            (fun scalar => MvPolynomial.C (constant scalar))) inputs 0) := by
      symm
      simpa [supportHomomorphism] using congrFun
        (Circuit.map_eval circuit
          (supportHomomorphism σ constant) inputs) 0
    _ = supportValue target := congrArg supportValue constructs

omit [Nontrivial R] in
/-- Arbitrary-depth multiplication lower bound under a circuit-local support
width promise. -/
theorem circuit_multiplication_lowerBound
    [DecidableEq σ]
    (constant : K → R)
    (inputs : Fin n → MvPolynomial σ R)
    (target : MvPolynomial σ R)
    (inputAvoid : ∀ witness : ↥(supportFinset target), ∀ input,
      witness.1 ∉ (supportValue (inputs input)).monomials)
    (constantAvoid : ∀ witness : ↥(supportFinset target), ∀ scalar,
      witness.1 ∉
        (constantSupport (σ := σ) (constant scalar)).monomials)
    (width : Nat)
    (positive : 0 < width)
    (circuit : Circuit (Algebraic.Arithmetic.signature K) n 1)
    (constructs :
      ({ inputCount := n, inputs := inputs, target := target } :
        Problem (MvPolynomial σ R)).Constructs circuit
          (Algebraic.Arithmetic.interpretation
            (fun scalar => MvPolynomial.C (constant scalar))))
    (widthBound : MultiplicationSupportWidthAtMost
      constant circuit inputs width) :
    target.support.card ⌈/⌉ (width * width) ≤
      circuit.cost
        (Algebraic.Arithmetic.multiplicationCost (K := K)) := by
  simpa using Support.circuit_multiplication_lowerBound
    (fun scalar => constantSupport (σ := σ) (constant scalar))
    (supportValue ∘ inputs) (supportFinset target)
    inputAvoid constantAvoid width positive circuit
    (constructs_support constant inputs target circuit constructs) widthBound

omit [Nontrivial R] in
/-- User-facing form using disjointness and a nonconstant target. -/
theorem circuit_multiplication_lowerBound_of_disjoint
    [DecidableEq σ]
    (constant : K → R)
    (inputs : Fin n → MvPolynomial σ R)
    (target : MvPolynomial σ R)
    (inputDisjoint : ∀ input,
      Disjoint target.support (inputs input).support)
    (target_nonconstant : 0 ∉ target.support)
    (width : Nat)
    (positive : 0 < width)
    (circuit : Circuit (Algebraic.Arithmetic.signature K) n 1)
    (constructs :
      ({ inputCount := n, inputs := inputs, target := target } :
        Problem (MvPolynomial σ R)).Constructs circuit
          (Algebraic.Arithmetic.interpretation
            (fun scalar => MvPolynomial.C (constant scalar))))
    (widthBound : MultiplicationSupportWidthAtMost
      constant circuit inputs width) :
    target.support.card ⌈/⌉ (width * width) ≤
      circuit.cost
        (Algebraic.Arithmetic.multiplicationCost (K := K)) :=
  circuit_multiplication_lowerBound constant inputs target
    (inputAvoid_of_disjoint inputs target inputDisjoint)
    (constantAvoid_of_zero_not_mem constant target target_nonconstant)
    width positive circuit constructs widthBound

end Circuit

end
end Exact
end MonotonePolynomial
end Arithmetic
end Fusion
end Algebraic
