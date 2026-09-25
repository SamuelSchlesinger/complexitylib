/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Fusion.Arithmetic.Interaction.Polynomial.Catalecticant.Rectangular.Degree
public import Complexitylib.Algebraic.LowerBound.Fusion.Arithmetic.Interaction.Rank.Occurrence

/-!
# Locally decomposable rectangular critical layers

If the degree-`d` homogeneous component of a multiplication output is a sum
of `r` degree-`d` Waring terms, every split-`k` catalecticant has rank at most
`r`.  This module supplies uniform and per-occurrence weighted forms of the
resulting `choose d k` Fusion lower bound.
-/

@[expose] public section

namespace Algebraic
namespace Fusion
namespace Arithmetic
namespace Interaction
namespace Polynomial
namespace Catalecticant
namespace Rectangular
namespace Decomposition

noncomputable section

variable {K : Type} {C : Type}

/-- The degree-`d` homogeneous component is a sum of at most `termCount`
degree-`d` powers. -/
def AtMost
    [Field K]
    (degree termCount : Nat)
    (polynomial : MvPolynomial (Fin degree) K) : Prop :=
  ∃ terms : Fin termCount → SumOfTerms.Waring.Rectangular.Term K degree,
    MvPolynomial.homogeneousComponent degree polynomial =
      ∑ index, SumOfTerms.Waring.Rectangular.termValue (terms index)

theorem zero_atMost
    [Field K]
    (degree termCount : Nat) :
    AtMost degree termCount (0 : MvPolynomial (Fin degree) K) := by
  let zeroTerm : SumOfTerms.Waring.Rectangular.Term K degree :=
    { scale := 0
      coefficients := fun _ => 0 }
  refine ⟨fun _ => zeroTerm, ?_⟩
  simp [zeroTerm, SumOfTerms.Waring.Rectangular.termValue]

theorem add
    [Field K]
    (degree leftCount rightCount : Nat)
    (left right : MvPolynomial (Fin degree) K)
    (leftDecomposes : AtMost degree leftCount left)
    (rightDecomposes : AtMost degree rightCount right) :
    AtMost degree (leftCount + rightCount) (left + right) := by
  obtain ⟨leftTerms, leftCritical⟩ := leftDecomposes
  obtain ⟨rightTerms, rightCritical⟩ := rightDecomposes
  refine ⟨Fin.addCases leftTerms rightTerms, ?_⟩
  rw [map_add, leftCritical, rightCritical, Fin.sum_univ_add]
  simp

theorem succ
    [Field K]
    (degree termCount : Nat)
    (polynomial : MvPolynomial (Fin degree) K)
    (decomposes : AtMost degree termCount polynomial) :
    AtMost degree (termCount + 1) polynomial := by
  obtain ⟨terms, critical⟩ := decomposes
  let zeroTerm : SumOfTerms.Waring.Rectangular.Term K degree :=
    { scale := 0
      coefficients := fun _ => 0 }
  refine ⟨Fin.lastCases zeroTerm terms, ?_⟩
  rw [critical, Fin.sum_univ_castSucc]
  simp [zeroTerm, SumOfTerms.Waring.Rectangular.termValue]

/-- An `r`-term critical-layer decomposition has rank at most `r` at every
split. -/
theorem feature_rank_le
    [Field K]
    [CharZero K]
    (degree split termCount : Nat)
    (polynomial : MvPolynomial (Fin degree) K)
    (decomposes : AtMost degree termCount polynomial) :
    LinearMap.rank
      (SumOfTerms.Waring.Rectangular.feature K degree split polynomial) ≤
        termCount := by
  obtain ⟨terms, critical⟩ := decomposes
  rw [← Degree.feature_homogeneousComponent degree split polynomial,
    critical, map_sum]
  calc
    LinearMap.rank
        (∑ index, SumOfTerms.Waring.Rectangular.feature K degree split
          (SumOfTerms.Waring.Rectangular.termValue (terms index))) ≤
      ∑ index, LinearMap.rank
        (SumOfTerms.Waring.Rectangular.feature K degree split
          (SumOfTerms.Waring.Rectangular.termValue (terms index))) := by
        simpa using LinearMap.rank_finsetSum_le
          (Finset.univ : Finset (Fin termCount))
          (fun index => SumOfTerms.Waring.Rectangular.feature K degree split
            (SumOfTerms.Waring.Rectangular.termValue (terms index)))
    _ ≤ ∑ _index : Fin termCount, (1 : Cardinal) := by
      apply Finset.sum_le_sum
      intro index _
      exact SumOfTerms.Waring.Rectangular.term_rank_le_one
        (terms index) split
    _ = termCount := by simp

/-- Evaluated multiplication occurrences for the degree-`d` squarefree
problem. -/
def multiplicationOccurrences
    [Field K]
    (constant : C → K)
    (degree : Nat)
    (circuit : Circuit (Algebraic.Arithmetic.signature C) degree 1) :
    List (Fin 2 → MvPolynomial (Fin degree) K) :=
  circuitMultiplicationArguments
    (fun scalar => MvPolynomial.C (constant scalar))
    (MvPolynomial.X : Fin degree → MvPolynomial (Fin degree) K)
    circuit

@[simp] theorem multiplicationOccurrences_length
    [Field K]
    (constant : C → K)
    (degree : Nat)
    (circuit : Circuit (Algebraic.Arithmetic.signature C) degree 1) :
    (multiplicationOccurrences constant degree circuit).length =
      circuit.cost
        (Algebraic.Arithmetic.multiplicationCost (K := C)) :=
  circuitMultiplicationArguments_length
    (fun scalar => MvPolynomial.C (constant scalar))
    (MvPolynomial.X : Fin degree → MvPolynomial (Fin degree) K)
    circuit

/-- Polynomial produced at one evaluated multiplication occurrence. -/
def multiplicationOutput
    [Field K]
    (constant : C → K)
    (degree : Nat)
    (circuit : Circuit (Algebraic.Arithmetic.signature C) degree 1)
    (index : Fin (multiplicationOccurrences constant degree circuit).length) :
    MvPolynomial (Fin degree) K :=
  let arguments :=
    (multiplicationOccurrences constant degree circuit).get index
  arguments (0 : Fin 2) * arguments (1 : Fin 2)

/-- A nonuniform decomposition budget for every multiplication occurrence. -/
def AtOccurrences
    [Field K]
    (constant : C → K)
    (degree : Nat)
    (circuit : Circuit (Algebraic.Arithmetic.signature C) degree 1)
    (budget : Fin (multiplicationOccurrences constant degree circuit).length →
      Nat) : Prop :=
  ∀ index,
    let arguments := (multiplicationOccurrences constant degree circuit).get index
    AtMost degree (budget index)
      (arguments (0 : Fin 2) * arguments (1 : Fin 2))

theorem occurrenceIndexedBound_of_atOccurrences
    [Field K]
    [CharZero K]
    (constant : C → K)
    (degree split : Nat)
    (degreeAtLeastTwo : 2 ≤ degree)
    (circuit : Circuit (Algebraic.Arithmetic.signature C) degree 1)
    (budget : Fin (multiplicationOccurrences constant degree circuit).length →
      Nat)
    (restricted : AtOccurrences constant degree circuit budget) :
    Rank.Occurrence.IndexedBound
      (certificate constant degree split degreeAtLeastTwo) circuit budget := by
  intro index
  change LinearMap.rank
    (SumOfTerms.Waring.Rectangular.feature K degree split
      (((multiplicationOccurrences constant degree circuit).get index)
          (0 : Fin 2) *
        ((multiplicationOccurrences constant degree circuit).get index)
          (1 : Fin 2))) ≤ budget index
  exact feature_rank_le degree split (budget index) _ (restricted index)

/-- Weighted rectangular Fusion bound over actual multiplication
occurrences. -/
theorem choose_le_sum_occurrenceBudget
    [Field K]
    [CharZero K]
    (constant : C → K)
    (degree split : Nat)
    (degreeAtLeastTwo : 2 ≤ degree)
    (circuit : Circuit (Algebraic.Arithmetic.signature C) degree 1)
    (constructs : (problem K degree).Constructs circuit
      (Algebraic.Arithmetic.interpretation
        (fun scalar => MvPolynomial.C (constant scalar))))
    (budget : Fin (multiplicationOccurrences constant degree circuit).length →
      Nat)
    (restricted : AtOccurrences constant degree circuit budget) :
    Nat.choose degree split ≤ ∑ index, budget index :=
  Rank.Occurrence.targetRank_le_sum_indexedBudget
    (certificate constant degree split degreeAtLeastTwo)
    (Nat.choose degree split)
    (SumOfTerms.Waring.Rectangular.target_rank_ge degree split)
    circuit constructs budget
    (occurrenceIndexedBound_of_atOccurrences constant degree split
      degreeAtLeastTwo circuit budget restricted)

/-- If the chosen layer is nonempty, some gate carries at least the ceiling
average rectangular decomposition budget. -/
theorem exists_occurrence_budget_ge_choose_ceilDiv
    [Field K]
    [CharZero K]
    (constant : C → K)
    (degree split : Nat)
    (degreeAtLeastTwo : 2 ≤ degree)
    (splitLe : split ≤ degree)
    (circuit : Circuit (Algebraic.Arithmetic.signature C) degree 1)
    (constructs : (problem K degree).Constructs circuit
      (Algebraic.Arithmetic.interpretation
        (fun scalar => MvPolynomial.C (constant scalar))))
    (budget : Fin (multiplicationOccurrences constant degree circuit).length →
      Nat)
    (restricted : AtOccurrences constant degree circuit budget) :
    ∃ index,
      Nat.choose degree split ⌈/⌉
          circuit.cost
            (Algebraic.Arithmetic.multiplicationCost (K := C)) ≤
        budget index := by
  simpa using
    Rank.Occurrence.exists_budget_ge_ceilDiv
      (Nat.choose degree split) (Nat.choose_pos splitLe) budget
      (choose_le_sum_occurrenceBudget constant degree split degreeAtLeastTwo
        circuit constructs budget restricted)

/-- Uniform decomposition restriction on every multiplication output. -/
def AtMultiplications
    [Field K]
    (constant : C → K)
    (degree : Nat)
    (circuit : Circuit (Algebraic.Arithmetic.signature C) degree 1)
    (termCount : Nat) : Prop :=
  ∀ arguments : Fin 2 → MvPolynomial (Fin degree) K,
    (⟨.mul, arguments⟩ : Atom (Algebraic.Arithmetic.signature C)
      (MvPolynomial (Fin degree) K)) ∈
        circuitAtoms circuit
          (Algebraic.Arithmetic.interpretation
            (fun scalar => MvPolynomial.C (constant scalar)))
          (MvPolynomial.X : Fin degree → MvPolynomial (Fin degree) K) →
    AtMost degree termCount
      (arguments (0 : Fin 2) * arguments (1 : Fin 2))

theorem multiplicationOutputRankAtMost_of_atMultiplications
    [Field K]
    [CharZero K]
    (constant : C → K)
    (degree split : Nat)
    (degreeAtLeastTwo : 2 ≤ degree)
    (circuit : Circuit (Algebraic.Arithmetic.signature C) degree 1)
    (termCount : Nat)
    (restricted : AtMultiplications constant degree circuit termCount) :
    MultiplicationOutputRankAtMost constant degree split degreeAtLeastTwo
      circuit termCount := by
  intro arguments present
  change LinearMap.rank
    (SumOfTerms.Waring.Rectangular.feature K degree split
      (arguments (0 : Fin 2) * arguments (1 : Fin 2))) ≤ termCount
  exact feature_rank_le degree split termCount _
    (restricted arguments present)

/-- Uniform locally decomposable critical layers yield the rectangular
rank/cost tradeoff. -/
theorem choose_ceilDiv_lowerBound
    [Field K]
    [CharZero K]
    (constant : C → K)
    (degree split : Nat)
    (degreeAtLeastTwo : 2 ≤ degree)
    (termCount : Nat)
    (termCountPositive : 0 < termCount)
    (circuit : Circuit (Algebraic.Arithmetic.signature C) degree 1)
    (constructs : (problem K degree).Constructs circuit
      (Algebraic.Arithmetic.interpretation
        (fun scalar => MvPolynomial.C (constant scalar))))
    (restricted : AtMultiplications constant degree circuit termCount) :
    Nat.choose degree split ⌈/⌉ termCount ≤
      circuit.cost
        (Algebraic.Arithmetic.multiplicationCost (K := C)) :=
  Rectangular.choose_ceilDiv_lowerBound constant degree split degreeAtLeastTwo
    termCount termCountPositive circuit constructs
    (localRankAtMost_of_multiplicationOutputRankAtMost constant degree split
      degreeAtLeastTwo circuit termCount
      (multiplicationOutputRankAtMost_of_atMultiplications constant degree split
        degreeAtLeastTwo circuit termCount restricted))

end
end Decomposition
end Rectangular
end Catalecticant
end Polynomial
end Interaction
end Arithmetic
end Fusion
end Algebraic
