/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Fusion.SumOfTerms.Rank
public import Mathlib.Data.Finset.Slice
public import Mathlib.Data.Nat.Choose.Central
public import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Matrix-flattening fusion lower bounds

The identity matrix has full rank, whereas an outer product has rank at most
one.  Instantiating the generic sum-of-terms rank certificate therefore proves
that a circuit expressing an `N × N` identity flattening as a sum of charged
rank-one terms needs at least `N` terms.

Taking the index set to be the middle layer of the Boolean lattice gives the
explicit lower bound `choose (2 * n) n`.  Mathlib's central-binomial estimate
then makes the exponential growth formal.
-/

@[expose] public section

namespace Algebraic
namespace Fusion
namespace SumOfTerms
namespace MatrixRank

/-- Parameters of one rank-one outer-product term. -/
structure Term (K : Type u) (I : Type u) where
  /-- Column vector of the outer product. -/
  left : I → K
  /-- Row vector of the outer product. -/
  right : I → K

/-- Matrix represented by a rank-one term. -/
def termValue
    [Mul K]
    (term : Term K I) : Matrix I I K :=
  Matrix.vecMulVec term.left term.right

/-- Construct the identity matrix with no free inputs. -/
abbrev identityProblem
    (K : Type u)
    (I : Type u)
    [Zero K]
    [One K]
    [DecidableEq I] : Problem (Matrix I I K) where
  inputCount := 0
  inputs := fun input => Fin.elim0 input
  target := 1

/-- An outer-product term has flattening rank at most one. -/
theorem rank_termValue_le_one
    {K : Type u}
    {I : Type u}
    [Field K]
    [Fintype I]
    [DecidableEq I]
    (term : Term K I) :
    LinearMap.rank (Matrix.toLin' (termValue term)) ≤ 1 := by
  unfold termValue
  exact Matrix.rank_vecMulVec (K := K) (m := I) (n := I)
    term.left term.right

/-- The identity flattening has rank equal to the size of its index type. -/
theorem card_le_rank_identity
    (K : Type u)
    (I : Type u)
    [Field K]
    [Fintype I]
    [DecidableEq I] :
    (Fintype.card I : Cardinal) ≤
      LinearMap.rank (Matrix.toLin' (1 : Matrix I I K)) := by
  rw [Matrix.toLin'_one]
  change (Fintype.card I : Cardinal) ≤
    Module.rank K ↥(LinearMap.range (LinearMap.id : (I → K) →ₗ[K] (I → K)))
  rw [LinearMap.range_id, rank_top, rank_fun']

/-- Matrix multiplication on vectors is the flattening feature. -/
noncomputable def identityCertificate
    (K : Type u)
    (I : Type u)
    [Field K]
    [Fintype I]
    [DecidableEq I] :
    RankCertificate (K := K) (A := I → K) (B := I → K)
      (termValue (K := K) (I := I)) (identityProblem K I) where
  feature := (Matrix.toLin' (R := K) (m := I) (n := I)).toLinearMap
  targetRank := Fintype.card I
  termRank := 1
  input_zero := by
    intro input
    exact Fin.elim0 input
  term_rank_le := by
    intro term
    change LinearMap.rank
      (Matrix.toLin' (Matrix.vecMulVec term.left term.right)) ≤ 1
    exact rank_termValue_le_one term
  target_rank_ge := by
    change (Fintype.card I : Cardinal) ≤
      LinearMap.rank (Matrix.toLin' (1 : Matrix I I K))
    exact card_le_rank_identity K I

@[simp] theorem identityCertificate_targetRank
    (K : Type u)
    (I : Type u)
    [Field K]
    [Fintype I]
    [DecidableEq I] :
    (identityCertificate K I).targetRank = Fintype.card I := rfl

@[simp] theorem identityCertificate_termRank
    (K : Type u)
    (I : Type u)
    [Field K]
    [Fintype I]
    [DecidableEq I] :
    (identityCertificate K I).termRank = 1 := rfl

/-- Full matrix rank forces one charged term for every index. -/
theorem identity_lowerBound
    {K : Type u}
    {I : Type u}
    [Field K]
    [Fintype I]
    [DecidableEq I]
    (circuit : Circuit
      (Algebraic.SumOfTerms.signature (Term K I)) 0 g 1)
    (constructs : (identityProblem K I).Constructs circuit
      (Algebraic.SumOfTerms.interpretation
        (termValue (K := K) (I := I)))) :
    Fintype.card I ≤
      circuit.cost (Algebraic.SumOfTerms.termCost (T := Term K I)) := by
  simpa using
    (identityCertificate K I).circuit_lowerBound (by simp) circuit constructs

/-- The type of `k`-subsets of an `n`-element set. -/
abbrev Layer (n k : Nat) : Type :=
  ↥(Finset.powersetCard k (Finset.univ : Finset (Fin n)))

theorem card_layer (n k : Nat) :
    Fintype.card (Layer n k) = Nat.choose n k := by
  simp [Layer]

/-- The Boolean-lattice layer flattening gives a binomial term lower bound. -/
theorem layer_lowerBound
    {K : Type}
    [Field K]
    (n k : Nat)
    (circuit : Circuit
      (Algebraic.SumOfTerms.signature (Term K (Layer n k))) 0 g 1)
    (constructs : (identityProblem K (Layer n k)).Constructs circuit
      (Algebraic.SumOfTerms.interpretation
        (termValue (K := K) (I := Layer n k)))) :
    Nat.choose n k ≤
      circuit.cost
        (Algebraic.SumOfTerms.termCost (T := Term K (Layer n k))) := by
  simpa using identity_lowerBound circuit constructs

/-- The middle-layer flattening needs the central binomial number of terms. -/
theorem centralBinom_lowerBound
    {K : Type}
    [Field K]
    (n : Nat)
    (circuit : Circuit
      (Algebraic.SumOfTerms.signature (Term K (Layer (2 * n) n))) 0 g 1)
    (constructs : (identityProblem K (Layer (2 * n) n)).Constructs circuit
      (Algebraic.SumOfTerms.interpretation
        (termValue (K := K) (I := Layer (2 * n) n)))) :
    Nat.centralBinom n ≤
      circuit.cost
        (Algebraic.SumOfTerms.termCost
          (T := Term K (Layer (2 * n) n))) := by
  simpa [Nat.centralBinom] using layer_lowerBound (K := K) (2 * n) n
    circuit constructs

/-- A fully explicit exponential consequence of the middle-layer rank bound. -/
theorem four_pow_lt_mul_cost
    {K : Type}
    [Field K]
    (n : Nat)
    (n_big : 4 ≤ n)
    (circuit : Circuit
      (Algebraic.SumOfTerms.signature (Term K (Layer (2 * n) n))) 0 g 1)
    (constructs : (identityProblem K (Layer (2 * n) n)).Constructs circuit
      (Algebraic.SumOfTerms.interpretation
        (termValue (K := K) (I := Layer (2 * n) n)))) :
    4 ^ n < n * circuit.cost
      (Algebraic.SumOfTerms.termCost
        (T := Term K (Layer (2 * n) n))) :=
  (Nat.four_pow_lt_mul_centralBinom n n_big).trans_le
    (Nat.mul_le_mul_left n
      (centralBinom_lowerBound n circuit constructs))

end MatrixRank
end SumOfTerms
end Fusion
end Algebraic
