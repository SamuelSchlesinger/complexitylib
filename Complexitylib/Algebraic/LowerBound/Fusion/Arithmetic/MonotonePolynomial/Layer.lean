/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Fusion.Arithmetic.MonotonePolynomial
public import Mathlib.Data.Finsupp.Indicator
public import Mathlib.Data.Nat.Choose.Central

/-!
# Squarefree-layer lower bounds for monotone polynomial circuits

The degree-`k` squarefree layer in `n` variables has exactly `choose n k`
monomials.  Its support is disjoint from the individual variable generators
when `k ≥ 2`, and it has no constant monomial.  The arbitrary-depth support
fusion theorem therefore yields a binomial multiplication lower bound for
circuits whose multiplication inputs have bounded support width.

At the middle layer this becomes a central-binomial bound and, using Mathlib's
explicit estimate, an exponential size-width tradeoff.
-/

@[expose] public section

namespace Algebraic
namespace Fusion
namespace Arithmetic
namespace MonotonePolynomial
namespace Layer

open scoped BigOperators

noncomputable section

/-- The type of `k`-subsets of an `n`-element variable set. -/
abbrev Index (n k : Nat) : Type :=
  ↥(Finset.powersetCard k (Finset.univ : Finset (Fin n)))

theorem card_index (n k : Nat) :
    Fintype.card (Index n k) = Nat.choose n k := by
  simp [Index]

/-- Squarefree exponent vector associated to one layer element. -/
def exponent
    (set : Index n k) : Fin n →₀ ℕ :=
  Finsupp.indicator set.1 fun _ _ => 1

@[simp] theorem exponent_apply
    (set : Index n k)
    (coordinate : Fin n) :
    exponent set coordinate = if coordinate ∈ set.1 then 1 else 0 := by
  simp [exponent, Finsupp.indicator_apply]

/-- Total degree of a layer exponent. -/
theorem exponent_sum
    (set : Index n k) :
    (exponent set).sum (fun _ multiplicity => multiplicity) = k := by
  unfold exponent
  rw [Finsupp.sum_indicator_index (s := set.1) (fun _ => (1 : Nat))
    (h := fun _ multiplicity => multiplicity) (by intros; rfl)]
  simpa using (Finset.mem_powersetCard.1 set.2).2

/-- Distinct subsets give distinct squarefree exponent vectors. -/
theorem exponent_injective :
    Function.Injective (exponent : Index n k → Fin n →₀ ℕ) := by
  intro left right equal
  apply Subtype.ext
  ext coordinate
  have pointwise := DFunLike.congr_fun equal coordinate
  by_cases inLeft : coordinate ∈ left.1 <;>
    by_cases inRight : coordinate ∈ right.1 <;>
      simp [exponent_apply, inLeft, inRight] at pointwise ⊢

/-- Embedding of the layer into exponent vectors. -/
def exponentEmbedding (n k : Nat) : Index n k ↪ (Fin n →₀ ℕ) where
  toFun := exponent
  inj' := exponent_injective

/-- Finite set of all squarefree degree-`k` exponent vectors. -/
def exponents (n k : Nat) : Finset (Fin n →₀ ℕ) :=
  Finset.univ.map (exponentEmbedding n k)

@[simp] theorem card_exponents (n k : Nat) :
    (exponents n k).card = Nat.choose n k := by
  simp [exponents]

/-- One monomial in the squarefree layer. -/
def monomial
    (set : Index n k) : MvPolynomial (Fin n) ℕ :=
  MvPolynomial.monomial (exponent set) 1

/-- Sum of all squarefree monomials of degree `k` in `n` variables. -/
def polynomial (n k : Nat) : MvPolynomial (Fin n) ℕ :=
  ∑ set : Index n k, monomial set

/-- Exact support of a finite sum over natural coefficients. -/
theorem support_finset_sum
    [DecidableEq σ]
    (indices : Finset ι)
    (term : ι → MvPolynomial σ ℕ) :
    (∑ index ∈ indices, term index).support =
      indices.biUnion fun index => (term index).support := by
  classical
  induction indices using Finset.induction_on with
  | empty => simp
  | @insert index indices absent inductionHypothesis =>
      simp [absent, inductionHypothesis, polynomial_support_add]

/-- The squarefree-layer polynomial has exactly the expected exponent
support. -/
theorem support_polynomial (n k : Nat) :
    (polynomial n k).support = exponents n k := by
  classical
  unfold polynomial
  rw [support_finset_sum]
  ext candidate
  simp [monomial, exponents, exponentEmbedding,
    MvPolynomial.support_monomial, eq_comm]

@[simp] theorem card_support_polynomial (n k : Nat) :
    (polynomial n k).support.card = Nat.choose n k := by
  rw [support_polynomial, card_exponents]

/-- A positive-degree squarefree layer has no constant monomial. -/
theorem zero_not_mem_support_polynomial
    (positive : 0 < k) :
    0 ∉ (polynomial n k).support := by
  rw [support_polynomial]
  intro present
  obtain ⟨set, _, equal⟩ := Finset.mem_map.mp present
  have sumEqual := congrArg
    (fun exponent : Fin n →₀ ℕ =>
      exponent.sum (fun _ multiplicity => multiplicity)) equal
  change (exponent set).sum (fun _ multiplicity => multiplicity) = _ at sumEqual
  rw [exponent_sum] at sumEqual
  simp at sumEqual
  omega

/-- When `k ≥ 2`, the target layer support is disjoint from each individual
variable support. -/
theorem support_polynomial_disjoint_X
    (two_le : 2 ≤ k)
    (coordinate : Fin n) :
    Disjoint (polynomial n k).support
      (MvPolynomial.X coordinate : MvPolynomial (Fin n) ℕ).support := by
  rw [Finset.disjoint_left]
  intro candidate targetPresent variablePresent
  rw [support_polynomial] at targetPresent
  obtain ⟨set, _, targetEqual⟩ := Finset.mem_map.mp targetPresent
  rw [MvPolynomial.support_X] at variablePresent
  have variableEqual : candidate = Finsupp.single coordinate 1 :=
    Finset.mem_singleton.mp variablePresent
  have exponentEqual : exponent set = Finsupp.single coordinate 1 := by
    change exponent set = candidate at targetEqual
    exact targetEqual.trans variableEqual
  have sumEqual := congrArg
    (fun exponent : Fin n →₀ ℕ =>
      exponent.sum (fun _ multiplicity => multiplicity)) exponentEqual
  rw [exponent_sum] at sumEqual
  simp at sumEqual
  omega

/-- Construct the squarefree layer from the individual variables. -/
abbrev problem (n k : Nat) : Problem (MvPolynomial (Fin n) ℕ) where
  inputCount := n
  inputs := MvPolynomial.X
  target := polynomial n k

/-- A bounded multiplication-input support width gives the binomial lower
bound for the squarefree layer, at arbitrary circuit depth. -/
theorem multiplication_lowerBound
    (two_le : 2 ≤ k)
    (width : Nat)
    (positive : 0 < width)
    (circuit : Circuit (Algebraic.Arithmetic.signature ℕ) n g 1)
    (constructs : (problem n k).Constructs circuit
      (Algebraic.Arithmetic.interpretation MvPolynomial.C))
    (widthBound : MultiplicationSupportWidthAtMost circuit
      (MvPolynomial.X : Fin n → MvPolynomial (Fin n) ℕ) width) :
    Nat.choose n k ⌈/⌉ (width * width) ≤
      circuit.cost
        (Algebraic.Arithmetic.multiplicationCost (K := ℕ)) := by
  simpa using circuit_multiplication_lowerBound_of_disjoint
    (MvPolynomial.X : Fin n → MvPolynomial (Fin n) ℕ)
    (polynomial n k)
    (support_polynomial_disjoint_X two_le)
    (zero_not_mem_support_polynomial (by omega : 0 < k))
    width positive circuit constructs widthBound

/-- The middle squarefree layer gives a central-binomial lower bound. -/
theorem centralBinom_multiplication_lowerBound
    (n : Nat)
    (two_le : 2 ≤ n)
    (width : Nat)
    (positive : 0 < width)
    (circuit : Circuit (Algebraic.Arithmetic.signature ℕ) (2 * n) g 1)
    (constructs : (problem (2 * n) n).Constructs circuit
      (Algebraic.Arithmetic.interpretation MvPolynomial.C))
    (widthBound : MultiplicationSupportWidthAtMost circuit
      (MvPolynomial.X : Fin (2 * n) → MvPolynomial (Fin (2 * n)) ℕ)
      width) :
    Nat.centralBinom n ⌈/⌉ (width * width) ≤
      circuit.cost
        (Algebraic.Arithmetic.multiplicationCost (K := ℕ)) := by
  simpa [Nat.centralBinom] using
    multiplication_lowerBound (n := 2 * n) (k := n) two_le width positive
      circuit constructs widthBound

/-- Explicit exponential size-width tradeoff for the middle squarefree
layer. -/
theorem four_pow_lt_mul_width_sq_cost
    (n : Nat)
    (n_big : 4 ≤ n)
    (width : Nat)
    (positive : 0 < width)
    (circuit : Circuit (Algebraic.Arithmetic.signature ℕ) (2 * n) g 1)
    (constructs : (problem (2 * n) n).Constructs circuit
      (Algebraic.Arithmetic.interpretation MvPolynomial.C))
    (widthBound : MultiplicationSupportWidthAtMost circuit
      (MvPolynomial.X : Fin (2 * n) → MvPolynomial (Fin (2 * n)) ℕ)
      width) :
    4 ^ n < n * ((width * width) *
      circuit.cost
        (Algebraic.Arithmetic.multiplicationCost (K := ℕ))) := by
  have capacityPositive : 0 < width * width := Nat.mul_pos positive positive
  have centralLe : Nat.centralBinom n ≤
      (width * width) * circuit.cost
        (Algebraic.Arithmetic.multiplicationCost (K := ℕ)) :=
    (ceilDiv_le_iff_le_mul capacityPositive).1
      (centralBinom_multiplication_lowerBound n (by omega) width positive
        circuit constructs widthBound)
  exact (Nat.four_pow_lt_mul_centralBinom n n_big).trans_le
    (Nat.mul_le_mul_left n centralLe)

end
end Layer
end MonotonePolynomial
end Arithmetic
end Fusion
end Algebraic
