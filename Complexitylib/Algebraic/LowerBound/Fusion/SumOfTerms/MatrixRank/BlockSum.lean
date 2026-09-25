/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Fusion.SumOfTerms.WeightedRank
public import Complexitylib.Algebraic.LowerBound.Fusion.SumOfTerms.MatrixRank.Block

/-!
# Weighted block-sum circuit lower bounds

A dictionary term is now an arbitrary matrix equipped with finite row and
column covers.  The term is charged the smaller cover size, addition is free,
and the target is the identity matrix.  The term-dependent weighted rank
engine proves that every constructing circuit pays at least the full matrix
dimension.

On the middle Boolean layer this gives an unconditional central-binomial, and
hence exponential, lower bound for weighted block-sum circuits.
-/

@[expose] public section

namespace Algebraic
namespace Fusion
namespace SumOfTerms
namespace MatrixRank
namespace BlockSum

noncomputable section

variable {K I : Type}
variable [Field K] [Fintype I] [DecidableEq I]

/-- Dictionary of row/column-supported square matrix blocks. -/
abbrev Term (K I : Type)
    [Field K] [Fintype I] [DecidableEq I] :=
  Block.Piece K I I

/-- Matrix denoted by a supported block term. -/
def termValue (term : Term K I) : Matrix I I K :=
  term.matrix

/-- Smaller-side charge of a supported block term. -/
def termWeight (term : Term K I) : Nat :=
  term.rankBudget

/-- Term-dependent operation cost for block-sum circuits. -/
def blockCost : OperationCost (Algebraic.SumOfTerms.signature (Term K I)) :=
  Algebraic.SumOfTerms.dictionaryCost (termWeight (K := K) (I := I))

@[simp] theorem blockCost_add :
    blockCost (K := K) (I := I) .add = 0 := rfl

@[simp] theorem blockCost_term (term : Term K I) :
    blockCost (.term term) = term.rankBudget := rfl

/-- Weighted rank certificate for the identity matrix. -/
def certificate :
    WeightedRank.Certificate (K := K) (A := I → K) (B := I → K)
      (termValue (K := K) (I := I))
      (termWeight (K := K) (I := I))
      (identityProblem K I) where
  feature := (Matrix.toLin' (R := K) (m := I) (n := I)).toLinearMap
  targetRank := Fintype.card I
  input_zero := by
    intro input
    exact Fin.elim0 input
  term_rank_le := by
    intro term
    change LinearMap.rank (Matrix.toLin' term.matrix) ≤ term.rankBudget
    exact term.rank_toLin'_le_rankBudget
  target_rank_ge := by
    change (Fintype.card I : Cardinal) ≤
      LinearMap.rank (Matrix.toLin' (1 : Matrix I I K))
    exact card_le_rank_identity K I

@[simp] theorem certificate_targetRank :
    (certificate (K := K) (I := I)).targetRank = Fintype.card I := rfl

/-- Any weighted sum-of-blocks circuit constructing the identity pays at
least the matrix dimension. -/
theorem identity_lowerBound
    (circuit : Circuit
      (Algebraic.SumOfTerms.signature (Term K I)) 0 1)
    (constructs : (identityProblem K I).Constructs circuit
      (Algebraic.SumOfTerms.interpretation
        (termValue (K := K) (I := I)))) :
    Fintype.card I ≤ circuit.cost (blockCost (K := K) (I := I)) := by
  simpa [blockCost] using
    (certificate (K := K) (I := I)).circuit_lowerBound circuit constructs

/-- Boolean-layer identity blocks require weighted cost `choose n k`. -/
theorem layer_lowerBound
    (n k : Nat)
    (circuit : Circuit
      (Algebraic.SumOfTerms.signature (Term K (Layer n k))) 0 1)
    (constructs : (identityProblem K (Layer n k)).Constructs circuit
      (Algebraic.SumOfTerms.interpretation
        (termValue (K := K) (I := Layer n k)))) :
    Nat.choose n k ≤
      circuit.cost (blockCost (K := K) (I := Layer n k)) := by
  simpa using identity_lowerBound circuit constructs

/-- Middle-layer weighted block-sum cost is at least the central binomial
coefficient. -/
theorem centralBinom_lowerBound
    (n : Nat)
    (circuit : Circuit
      (Algebraic.SumOfTerms.signature (Term K (Layer (2 * n) n))) 0 1)
    (constructs : (identityProblem K (Layer (2 * n) n)).Constructs circuit
      (Algebraic.SumOfTerms.interpretation
        (termValue (K := K) (I := Layer (2 * n) n)))) :
    Nat.centralBinom n ≤
      circuit.cost (blockCost (K := K) (I := Layer (2 * n) n)) := by
  simpa [Nat.centralBinom] using
    layer_lowerBound (K := K) (2 * n) n circuit constructs

/-- Explicit exponential lower bound for middle-layer weighted block-sum
circuits. -/
theorem four_pow_lt_n_mul_cost
    (n : Nat)
    (nBig : 4 ≤ n)
    (circuit : Circuit
      (Algebraic.SumOfTerms.signature (Term K (Layer (2 * n) n))) 0 1)
    (constructs : (identityProblem K (Layer (2 * n) n)).Constructs circuit
      (Algebraic.SumOfTerms.interpretation
        (termValue (K := K) (I := Layer (2 * n) n)))) :
    4 ^ n < n *
      circuit.cost (blockCost (K := K) (I := Layer (2 * n) n)) :=
  (Nat.four_pow_lt_mul_centralBinom n nBig).trans_le
    (Nat.mul_le_mul_left n (centralBinom_lowerBound n circuit constructs))

end
end BlockSum
end MatrixRank
end SumOfTerms
end Fusion
end Algebraic
