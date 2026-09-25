/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Fusion.SumOfTerms.Coverage
public import Mathlib.Data.Finset.Prod

/-!
# Rectangle-cover fusion bounds

This file specializes finite-support coverage fusion to combinatorial
rectangles.  An allowed term is a Cartesian product contained in the target
relation; addition takes unions of supports.  Thus the resulting circuits are
monotone sums of admissible product terms, equivalently exact rectangle covers.

A local upper bound on the size of an admissible rectangle gives a term-count
lower bound.  For the diagonal relation every admissible rectangle contains at
most one pair, so an exact cover needs one charged term per diagonal entry.
-/

@[expose] public section

namespace Algebraic
namespace Fusion
namespace SumOfTerms
namespace Rectangle

/-- A combinatorial rectangle whose whole support lies in the target
relation. -/
structure Term
    {L : Type u}
    {R : Type v}
    [DecidableEq L]
    [DecidableEq R]
    (target : Finset (L × R)) where
  /-- Left side of the rectangle. -/
  left : Finset L
  /-- Right side of the rectangle. -/
  right : Finset R
  /-- Admissibility prevents a monotone term from producing an off-target
  monomial. -/
  product_subset : left.product right ⊆ target

/-- The finite monomial support contributed by one rectangle term. -/
def termSupport
    {L : Type u}
    {R : Type v}
    [DecidableEq L]
    [DecidableEq R]
    {target : Finset (L × R)}
    (term : Term target) : Coverage.FiniteSupport (L × R) :=
  ⟨term.left.product term.right⟩

@[simp] theorem termSupport_monomials
    {L : Type u}
    {R : Type v}
    [DecidableEq L]
    [DecidableEq R]
    {target : Finset (L × R)}
    (term : Term target) :
    (termSupport term).monomials = term.left.product term.right := rfl

/-- A uniform size bound for admissible rectangles in a target relation. -/
structure Bound
    {L : Type u}
    {R : Type v}
    [DecidableEq L]
    [DecidableEq R]
    (target : Finset (L × R)) where
  /-- Maximum cardinality of one admissible rectangle. -/
  capacity : Nat
  /-- The local rectangle-size estimate. -/
  rectangle_card_le : ∀ term : Term target,
    (term.left.product term.right).card ≤ capacity

/-- The witnesses covered by a rectangle inject into its Cartesian-product
support. -/
theorem coveredWitnesses_card_le_product
    {L : Type u}
    {R : Type v}
    [DecidableEq L]
    [DecidableEq R]
    {target : Finset (L × R)}
    (term : Term target) :
    (Coverage.coveredWitnesses target termSupport term).card ≤
      (term.left.product term.right).card := by
  classical
  apply Finset.card_le_card_of_injOn Subtype.val
  · intro witness present
    exact (Coverage.mem_coveredWitnesses target termSupport term witness).mp present
  · intro left _ right _ equal
    exact Subtype.ext equal

/-- Rectangle-size bounds are finite-support coverage bounds. -/
noncomputable def Bound.coverageBound
    {L : Type u}
    {R : Type v}
    [DecidableEq L]
    [DecidableEq R]
    {target : Finset (L × R)}
    (bound : Bound target) : Coverage.Bound target
      (termSupport (target := target)) where
  capacity := bound.capacity
  covered_card_le := by
    intro term
    exact (coveredWitnesses_card_le_product term).trans
      (bound.rectangle_card_le term)

@[simp] theorem Bound.coverageBound_capacity
    {L : Type u}
    {R : Type v}
    [DecidableEq L]
    [DecidableEq R]
    {target : Finset (L × R)}
    (bound : Bound target) :
    bound.coverageBound.capacity = bound.capacity := rfl

/-- Every exact monotone rectangle cover has the expected cardinality lower
bound. -/
theorem Bound.circuit_lowerBound
    {L : Type u}
    {R : Type v}
    [DecidableEq L]
    [DecidableEq R]
    {target : Finset (L × R)}
    (bound : Bound target)
    (positive : 0 < bound.capacity)
    (circuit : Circuit
      (Algebraic.SumOfTerms.signature (Term target)) 0 1)
    (constructs : (Coverage.problem target).Constructs circuit
      (Algebraic.SumOfTerms.interpretation termSupport)) :
    target.card ⌈/⌉ bound.capacity ≤
      circuit.cost
        (Algebraic.SumOfTerms.termCost (T := Term target)) := by
  simpa using bound.coverageBound.circuit_lowerBound
    (by simpa using positive) circuit constructs

/-- Embedding used to enumerate the diagonal relation without duplicates. -/
def diagonalEmbedding (I : Type u) : I ↪ I × I where
  toFun index := (index, index)
  inj' := by
    intro left right equal
    exact congrArg Prod.fst equal

/-- The finite diagonal relation on an index type. -/
def diagonal
    (I : Type u)
    [Fintype I] : Finset (I × I) :=
  Finset.univ.map (diagonalEmbedding I)

@[simp] theorem card_diagonal
    (I : Type u)
    [Fintype I] :
    (diagonal I).card = Fintype.card I := by
  simp [diagonal]

@[simp] theorem mem_diagonal
    {I : Type u}
    [Fintype I]
    (pair : I × I) :
    pair ∈ diagonal I ↔ pair.1 = pair.2 := by
  classical
  constructor
  · intro present
    simp only [diagonal, Finset.mem_map] at present
    obtain ⟨index, _, equal⟩ := present
    rw [← equal]
    rfl
  · intro equal
    apply Finset.mem_map.mpr
    refine ⟨pair.1, Finset.mem_univ _, ?_⟩
    apply Prod.ext
    · rfl
    · exact equal

/-- A rectangle contained in the diagonal has at most one pair. -/
theorem diagonal_rectangle_card_le_one
    {I : Type u}
    [Fintype I]
    [DecidableEq I]
    (term : Term (diagonal I)) :
    (term.left.product term.right).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro first first_mem second second_mem
  rcases first with ⟨firstLeft, firstRight⟩
  rcases second with ⟨secondLeft, secondRight⟩
  have first_diagonal : firstLeft = firstRight :=
    (mem_diagonal _).mp (term.product_subset first_mem)
  have second_diagonal : secondLeft = secondRight :=
    (mem_diagonal _).mp (term.product_subset second_mem)
  have first_product : firstLeft ∈ term.left := by
    simpa using (Finset.mem_product.mp first_mem).1
  have second_product : secondRight ∈ term.right := by
    simpa using (Finset.mem_product.mp second_mem).2
  have cross_diagonal : firstLeft = secondRight :=
    (mem_diagonal (I := I) (firstLeft, secondRight)).mp (term.product_subset
      (Finset.mem_product.mpr ⟨first_product, second_product⟩))
  apply Prod.ext
  · exact cross_diagonal.trans second_diagonal.symm
  · exact first_diagonal.symm.trans cross_diagonal

/-- Capacity-one certificate for the finite diagonal relation. -/
noncomputable def diagonalBound
    (I : Type u)
    [Fintype I]
    [DecidableEq I] : Bound (diagonal I) where
  capacity := 1
  rectangle_card_le := diagonal_rectangle_card_le_one

@[simp] theorem diagonalBound_capacity
    (I : Type u)
    [Fintype I]
    [DecidableEq I] :
    (diagonalBound I).capacity = 1 := rfl

/-- An exact monotone sum of diagonal-contained product terms needs one term
per diagonal monomial. -/
theorem diagonal_lowerBound
    {I : Type u}
    [Fintype I]
    [DecidableEq I]
    (circuit : Circuit
      (Algebraic.SumOfTerms.signature (Term (diagonal I))) 0 1)
    (constructs : (Coverage.problem (diagonal I)).Constructs circuit
      (Algebraic.SumOfTerms.interpretation termSupport)) :
    Fintype.card I ≤
      circuit.cost
        (Algebraic.SumOfTerms.termCost (T := Term (diagonal I))) := by
  have positive : 0 < (diagonalBound I).capacity := by
    change 0 < 1
    exact Nat.zero_lt_succ 0
  simpa using (diagonalBound I).circuit_lowerBound
    positive circuit constructs

end Rectangle
end SumOfTerms
end Fusion
end Algebraic
