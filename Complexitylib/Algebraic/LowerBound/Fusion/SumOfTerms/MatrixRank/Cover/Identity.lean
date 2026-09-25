/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Fusion.SumOfTerms.MatrixRank.Cover

/-!
# Weighted rectangle covers of identity flattenings

Every rectangle cover of the nonzero support of an identity matrix has total
weight at least the matrix dimension, where a rectangle's weight is the
smaller of its row and column cardinalities.  If every rectangle has weight at
most `r`, this gives the count bound `ceil(dimension / r)`.

The middle Boolean layer turns these statements into central-binomial and
explicit exponential lower bounds for two-dimensional covers.
-/

@[expose] public section

namespace Algebraic
namespace Fusion
namespace SumOfTerms
namespace MatrixRank
namespace Cover
namespace Identity

noncomputable section

open Cardinal

variable {K I : Type}
variable [Field K] [Fintype I] [DecidableEq I]

/-- Weighted size of every rectangle cover of an identity matrix is at least
the matrix dimension. -/
theorem card_le_rankBudget
    (certificate : Certificate (1 : Matrix I I K)) :
    Fintype.card I ≤ certificate.rankBudget := by
  have cardinalBound : (Fintype.card I : Cardinal) ≤
      (certificate.rankBudget : Cardinal) :=
    (card_le_rank_identity K I).trans
      certificate.rank_toLin'_le_rankBudget
  exact_mod_cast cardinalBound

omit [Fintype I] in
/-- A uniform per-rectangle capacity bounds total cover weight by rectangle
count times capacity. -/
theorem rankBudget_le_rectangleCount_mul_capacity
    (certificate : Certificate (1 : Matrix I I K))
    (capacity : Nat)
    (bounded : ∀ index,
      min (certificate.rows index).card
        (certificate.columns index).card ≤ capacity) :
    certificate.rankBudget ≤ certificate.rectangleCount * capacity := by
  unfold Certificate.rankBudget
  calc
    (∑ index, min (certificate.rows index).card
        (certificate.columns index).card) ≤
      ∑ _index : Fin certificate.rectangleCount, capacity := by
        apply Finset.sum_le_sum
        intro index _
        exact bounded index
    _ = certificate.rectangleCount * capacity := by simp

/-- Identity dimension is bounded by rectangle count times a uniform local
capacity. -/
theorem card_le_rectangleCount_mul_capacity
    (certificate : Certificate (1 : Matrix I I K))
    (capacity : Nat)
    (bounded : ∀ index,
      min (certificate.rows index).card
        (certificate.columns index).card ≤ capacity) :
    Fintype.card I ≤ certificate.rectangleCount * capacity :=
  (card_le_rankBudget certificate).trans
    (rankBudget_le_rectangleCount_mul_capacity certificate capacity bounded)

/-- Ceiling-divided rectangle-count lower bound. -/
theorem card_ceilDiv_le_rectangleCount
    (certificate : Certificate (1 : Matrix I I K))
    (capacity : Nat)
    (capacityPositive : 0 < capacity)
    (bounded : ∀ index,
      min (certificate.rows index).card
        (certificate.columns index).card ≤ capacity) :
    Fintype.card I ⌈/⌉ capacity ≤ certificate.rectangleCount :=
  (ceilDiv_le_iff_le_mul capacityPositive).2
    (by
      simpa [Nat.mul_comm] using
        card_le_rectangleCount_mul_capacity certificate capacity bounded)

/-- Middle-layer rectangle covers have central-binomial weighted size. -/
theorem centralBinom_le_rankBudget
    (n : Nat)
    (certificate : Certificate
      (1 : Matrix (Layer (2 * n) n) (Layer (2 * n) n) K)) :
    Nat.centralBinom n ≤ certificate.rankBudget := by
  simpa [Nat.centralBinom] using card_le_rankBudget certificate

/-- Uniform-capacity middle-layer rectangle covers need at least the
ceiling-divided central binomial number of rectangles. -/
theorem centralBinom_ceilDiv_le_rectangleCount
    (n : Nat)
    (certificate : Certificate
      (1 : Matrix (Layer (2 * n) n) (Layer (2 * n) n) K))
    (capacity : Nat)
    (capacityPositive : 0 < capacity)
    (bounded : ∀ index,
      min (certificate.rows index).card
        (certificate.columns index).card ≤ capacity) :
    Nat.centralBinom n ⌈/⌉ capacity ≤
      certificate.rectangleCount := by
  simpa [Nat.centralBinom] using
    card_ceilDiv_le_rectangleCount certificate capacity capacityPositive
      bounded

/-- Explicit exponential lower bound on total middle-layer cover weight. -/
theorem four_pow_lt_n_mul_rankBudget
    (n : Nat)
    (nBig : 4 ≤ n)
    (certificate : Certificate
      (1 : Matrix (Layer (2 * n) n) (Layer (2 * n) n) K)) :
    4 ^ n < n * certificate.rankBudget :=
  (Nat.four_pow_lt_mul_centralBinom n nBig).trans_le
    (Nat.mul_le_mul_left n (centralBinom_le_rankBudget n certificate))

/-- Explicit exponential count/capacity tradeoff for middle-layer rectangle
covers. -/
theorem four_pow_lt_n_mul_rectangleCount_mul_capacity
    (n : Nat)
    (nBig : 4 ≤ n)
    (certificate : Certificate
      (1 : Matrix (Layer (2 * n) n) (Layer (2 * n) n) K))
    (capacity : Nat)
    (bounded : ∀ index,
      min (certificate.rows index).card
        (certificate.columns index).card ≤ capacity) :
    4 ^ n < n * (certificate.rectangleCount * capacity) :=
  (four_pow_lt_n_mul_rankBudget n nBig certificate).trans_le
    (Nat.mul_le_mul_left n
      (rankBudget_le_rectangleCount_mul_capacity certificate capacity
        bounded))

end
end Identity
end Cover
end MatrixRank
end SumOfTerms
end Fusion
end Algebraic
