/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Fusion.Arithmetic.Progress.Separated.Polynomial
public import Complexitylib.Algebraic.LowerBound.Fusion.Arithmetic.Progress.Separated.Closure.Addition
public import Mathlib.Data.Finsupp.Indicator
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Data.Nat.Choose.Central

/-!
# Schnorr's clique-polynomial addition lower bound

For a `k`-element vertex set `S`, its clique monomial contains every ordered
edge in `S × S` (including diagonal variables).  The family of all such
monomials is separated: if `C × C` is contained in
`(A × A) ∪ (B × B)` and all three vertex sets have the same cardinality,
then `C = A` or `C = B`.

Combining this finite combinatorics with Schnorr's substitution-closed
separation measure proves that every polynomial with this support needs at
least `Nat.choose n k - 1` addition gates in every constant-free monotone
arithmetic circuit.  Taking a middle layer gives the classical exponential
family over `n²` variables.
-/

@[expose] public section

namespace Algebraic
namespace Fusion
namespace Arithmetic
namespace Progress
namespace Separated
namespace Clique

noncomputable section

/-- Encode an ordered pair of vertices as one of `n²` circuit inputs. -/
def edgeEmbedding (vertexCount : Nat) :
    Fin vertexCount × Fin vertexCount ↪ Fin (vertexCount * vertexCount) :=
  finProdFinEquiv.toEmbedding

/-- Ordered edges induced by a finite vertex set, represented in the flattened
`Fin (n²)` input space. -/
def edgeSet
    (vertices : Finset (Fin vertexCount)) :
    Finset (Fin (vertexCount * vertexCount)) :=
  (vertices ×ˢ vertices).map (edgeEmbedding vertexCount)

@[simp] theorem encoded_edge_mem_edgeSet
    (vertices : Finset (Fin vertexCount))
    (left right : Fin vertexCount) :
    edgeEmbedding vertexCount (left, right) ∈ edgeSet vertices ↔
      left ∈ vertices ∧ right ∈ vertices := by
  simp [edgeSet, edgeEmbedding]

/-- Characteristic exponent vector of the ordered clique on `vertices`. -/
def cliqueExponent
    (vertices : Finset (Fin vertexCount)) :
    Fin (vertexCount * vertexCount) →₀ ℕ :=
  Finsupp.indicator (edgeSet vertices) (fun _ _ => 1)

@[simp] theorem cliqueExponent_encoded_edge
    (vertices : Finset (Fin vertexCount))
    (left right : Fin vertexCount) :
    cliqueExponent vertices (edgeEmbedding vertexCount (left, right)) =
      if left ∈ vertices ∧ right ∈ vertices then 1 else 0 := by
  classical
  simp [cliqueExponent, Finsupp.indicator_apply]

/-- The diagonal coordinates recover the underlying vertex set. -/
theorem cliqueExponent_injective :
    Function.Injective
      (cliqueExponent (vertexCount := vertexCount)) := by
  classical
  intro left right equal
  ext vertex
  have diagonalEqual := DFunLike.congr_fun equal
    (edgeEmbedding vertexCount (vertex, vertex))
  by_cases leftPresent : vertex ∈ left <;>
    by_cases rightPresent : vertex ∈ right <;>
    simp [leftPresent, rightPresent] at diagonalEqual ⊢

/-- Embedding used to form the finite support of the clique polynomial. -/
def cliqueExponentEmbedding (vertexCount : Nat) :
    Finset (Fin vertexCount) ↪
      (Fin (vertexCount * vertexCount) →₀ ℕ) where
  toFun := cliqueExponent
  inj' := cliqueExponent_injective

/-- The exponent support of the `k`-clique polynomial on `vertexCount`
vertices. -/
def cliqueSupport
    (vertexCount cliqueSize : Nat) :
    Finset (Fin (vertexCount * vertexCount) →₀ ℕ) :=
  (Finset.univ.powersetCard cliqueSize).map
    (cliqueExponentEmbedding vertexCount)

@[simp] theorem card_cliqueSupport
    (vertexCount cliqueSize : Nat) :
    (cliqueSupport vertexCount cliqueSize).card =
      Nat.choose vertexCount cliqueSize := by
  simp [cliqueSupport]

/-- If every induced edge of `middle` belongs to the clique on `left` or the
clique on `right`, then all vertices of `middle` lie on one side. -/
private theorem subset_left_or_right_of_edgeSet_subset
    {left right middle : Finset (Fin vertexCount)}
    (subset : edgeSet middle ⊆ edgeSet left ∪ edgeSet right) :
    middle ⊆ left ∨ middle ⊆ right := by
  classical
  by_cases middleSubsetLeft : middle ⊆ left
  · exact Or.inl middleSubsetLeft
  · right
    obtain ⟨witness, witnessMiddle, witnessNotLeft⟩ :=
      Finset.not_subset.mp middleSubsetLeft
    intro vertex vertexMiddle
    have encodedPresent :
        edgeEmbedding vertexCount (witness, vertex) ∈ edgeSet middle := by
      simp [witnessMiddle, vertexMiddle]
    have encodedSide := subset encodedPresent
    rw [Finset.mem_union] at encodedSide
    rcases encodedSide with encodedLeft | encodedRight
    · have witnessLeft : witness ∈ left :=
        (encoded_edge_mem_edgeSet left witness vertex).mp encodedLeft |>.1
      exact (witnessNotLeft witnessLeft).elim
    · exact (encoded_edge_mem_edgeSet right witness vertex).mp
        encodedRight |>.2

/-- Coordinatewise divisibility of clique monomials implies the corresponding
containment of their induced edge sets. -/
private theorem edgeSet_subset_union_of_cliqueExponent_le
    {left right middle : Finset (Fin vertexCount)}
    (divides : cliqueExponent middle ≤
      cliqueExponent left + cliqueExponent right) :
    edgeSet middle ⊆ edgeSet left ∪ edgeSet right := by
  classical
  intro edge edgeMiddle
  rw [Finset.mem_union]
  by_contra absent
  push Not at absent
  have coordinateBound := divides edge
  simp [cliqueExponent, Finsupp.indicator_apply,
    edgeMiddle, absent.1, absent.2] at coordinateBound

/-- Equal-size clique exponent vectors satisfy Schnorr separation. -/
theorem vertices_eq_left_or_right_of_cliqueExponent_le
    {left right middle : Finset (Fin vertexCount)}
    (leftCard : left.card = cliqueSize)
    (rightCard : right.card = cliqueSize)
    (middleCard : middle.card = cliqueSize)
    (divides : cliqueExponent middle ≤
      cliqueExponent left + cliqueExponent right) :
    middle = left ∨ middle = right := by
  have edgeSubset :=
    edgeSet_subset_union_of_cliqueExponent_le divides
  rcases subset_left_or_right_of_edgeSet_subset edgeSubset with
      middleLeft | middleRight
  · left
    exact Finset.eq_of_subset_of_card_le middleLeft (by omega)
  · right
    exact Finset.eq_of_subset_of_card_le middleRight (by omega)

/-- All `k`-clique monomials form a separated family. -/
theorem cliqueSupport_isSeparated
    (vertexCount cliqueSize : Nat) :
    IsSeparated (cliqueSupport vertexCount cliqueSize)
      (cliqueSupport vertexCount cliqueSize) := by
  classical
  constructor
  · exact Finset.Subset.rfl
  · intro left leftPresent right rightPresent middle middlePresent
      middleLe
    obtain ⟨leftVertices, leftVerticesPresent, leftEqual⟩ :=
      Finset.mem_map.mp leftPresent
    obtain ⟨rightVertices, rightVerticesPresent, rightEqual⟩ :=
      Finset.mem_map.mp rightPresent
    obtain ⟨middleVertices, middleVerticesPresent, middleEqual⟩ :=
      Finset.mem_map.mp middlePresent
    change cliqueExponent leftVertices = left at leftEqual
    change cliqueExponent rightVertices = right at rightEqual
    change cliqueExponent middleVertices = middle at middleEqual
    subst left
    subst right
    subst middle
    have leftCard :=
      (Finset.mem_powersetCard.mp leftVerticesPresent).2
    have rightCard :=
      (Finset.mem_powersetCard.mp rightVerticesPresent).2
    have middleCard :=
      (Finset.mem_powersetCard.mp middleVerticesPresent).2
    rcases vertices_eq_left_or_right_of_cliqueExponent_le
        leftCard rightCard middleCard middleLe with equal | equal
    · exact Or.inl (congrArg cliqueExponent equal)
    · exact Or.inr (congrArg cliqueExponent equal)

/-- Schnorr's coefficient-one `k`-clique polynomial on ordered edge
variables. -/
def polynomial
    (vertexCount cliqueSize : Nat) :
    MvPolynomial (Fin (vertexCount * vertexCount)) ℕ :=
  Polynomial.ofSupport (cliqueSupport vertexCount cliqueSize)

@[simp] theorem polynomial_support
    (vertexCount cliqueSize : Nat) :
    (polynomial vertexCount cliqueSize).support =
      cliqueSupport vertexCount cliqueSize := by
  simp [polynomial]

/-- The clique polynomial has exactly `choose vertexCount cliqueSize`
monomials. -/
theorem card_polynomial_support
    (vertexCount cliqueSize : Nat) :
    (polynomial vertexCount cliqueSize).support.card =
      Nat.choose vertexCount cliqueSize := by
  simp

/-- Every polynomial with exactly the clique-monomial support needs
`choose vertexCount cliqueSize - 1` additions, independently of its positive
coefficients. -/
theorem circuit_addition_lowerBound_of_support_eq
    (target : MvPolynomial (Fin (vertexCount * vertexCount)) ℕ)
    (supportEqual : target.support =
      cliqueSupport vertexCount cliqueSize)
    (circuit : Circuit
      (Algebraic.Arithmetic.signature PEmpty)
        (vertexCount * vertexCount) 1)
    (constructs :
      ({ inputCount := vertexCount * vertexCount,
          inputs := MvPolynomial.X, target := target } :
        Problem (MvPolynomial (Fin (vertexCount * vertexCount)) ℕ)).Constructs
          circuit
          (polynomialInterpretation
            (Fin (vertexCount * vertexCount)))) :
    Nat.choose vertexCount cliqueSize - 1 ≤
      circuit.cost
        (Algebraic.Arithmetic.additionCost (K := PEmpty)) := by
  have targetSeparated : IsSeparated target.support target.support := by
    rw [supportEqual]
    exact cliqueSupport_isSeparated vertexCount cliqueSize
  have bound := Closure.Addition.circuit_addition_lowerBound_of_isSeparated
    target targetSeparated circuit constructs
  simpa [supportEqual] using bound

/-- Schnorr's addition lower bound for the clique polynomial. -/
theorem circuit_addition_lowerBound
    (circuit : Circuit
      (Algebraic.Arithmetic.signature PEmpty)
        (vertexCount * vertexCount) 1)
    (constructs :
      ({ inputCount := vertexCount * vertexCount,
          inputs := MvPolynomial.X,
          target := polynomial vertexCount cliqueSize } :
        Problem (MvPolynomial (Fin (vertexCount * vertexCount)) ℕ)).Constructs
          circuit
          (polynomialInterpretation
            (Fin (vertexCount * vertexCount)))) :
    Nat.choose vertexCount cliqueSize - 1 ≤
      circuit.cost
        (Algebraic.Arithmetic.additionCost (K := PEmpty)) :=
  circuit_addition_lowerBound_of_support_eq
    (polynomial vertexCount cliqueSize) (polynomial_support _ _)
    circuit constructs

/-- Middle-layer clique polynomials pay the central binomial coefficient,
minus one, in additions. -/
theorem central_circuit_addition_lowerBound
    (circuit : Circuit
      (Algebraic.Arithmetic.signature PEmpty)
        ((2 * halfVertices) * (2 * halfVertices)) 1)
    (constructs :
      ({ inputCount := (2 * halfVertices) * (2 * halfVertices),
          inputs := MvPolynomial.X,
          target := polynomial (2 * halfVertices) halfVertices } :
        Problem
          (MvPolynomial
            (Fin ((2 * halfVertices) * (2 * halfVertices))) ℕ)).Constructs
          circuit
          (polynomialInterpretation
            (Fin ((2 * halfVertices) * (2 * halfVertices))))) :
    Nat.centralBinom halfVertices - 1 ≤
      circuit.cost
        (Algebraic.Arithmetic.additionCost (K := PEmpty)) := by
  simpa [Nat.centralBinom] using
    (circuit_addition_lowerBound
      (vertexCount := 2 * halfVertices)
      (cliqueSize := halfVertices) circuit constructs)

/-- An explicit exponential form of the middle-layer lower bound.  For at
least eight vertices, `4^halfVertices` is strictly smaller than
`halfVertices` times one plus the circuit's addition count. -/
theorem central_circuit_exponential_lowerBound
    (halfVerticesBig : 4 ≤ halfVertices)
    (circuit : Circuit
      (Algebraic.Arithmetic.signature PEmpty)
        ((2 * halfVertices) * (2 * halfVertices)) 1)
    (constructs :
      ({ inputCount := (2 * halfVertices) * (2 * halfVertices),
          inputs := MvPolynomial.X,
          target := polynomial (2 * halfVertices) halfVertices } :
        Problem
          (MvPolynomial
            (Fin ((2 * halfVertices) * (2 * halfVertices))) ℕ)).Constructs
          circuit
          (polynomialInterpretation
            (Fin ((2 * halfVertices) * (2 * halfVertices))))) :
    4 ^ halfVertices <
      halfVertices *
        (circuit.cost
          (Algebraic.Arithmetic.additionCost (K := PEmpty)) + 1) := by
  have costBound := central_circuit_addition_lowerBound circuit constructs
  have centralLe : Nat.centralBinom halfVertices ≤
      circuit.cost
          (Algebraic.Arithmetic.additionCost (K := PEmpty)) + 1 := by
    have positive := Nat.centralBinom_pos halfVertices
    omega
  exact (Nat.four_pow_lt_mul_centralBinom halfVertices halfVerticesBig).trans_le
    (Nat.mul_le_mul_left halfVertices centralLe)

end
end Clique
end Separated
end Progress
end Arithmetic
end Fusion
end Algebraic
