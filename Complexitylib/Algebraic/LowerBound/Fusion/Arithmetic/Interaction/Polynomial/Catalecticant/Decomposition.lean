/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Fusion.Arithmetic.Interaction.Polynomial.Catalecticant.Degree
public import Complexitylib.Algebraic.LowerBound.Fusion.Arithmetic.Interaction.Rank.Occurrence

/-!
# Locally decomposable critical layers

Generalize the rank-one critical-layer restriction to multiplication outputs
whose degree-`2n` homogeneous component is a sum of `r` Waring terms.  Rank
subadditivity turns such a semantic decomposition into a local catalecticant
rank bound `r`, yielding the tradeoff

`centralBinom n / r ≤ multiplication cost`.

The `Fin r` presentation allows zero-scaled terms to pad shorter
decompositions, so it represents "at most `r`" terms over a field.
-/

@[expose] public section

namespace Algebraic
namespace Fusion
namespace Arithmetic
namespace Interaction
namespace Polynomial
namespace Catalecticant
namespace Decomposition

noncomputable section

open Cardinal

variable {K : Type} {C : Type}

/-- The critical homogeneous layer is a sum of at most `termCount` Waring
terms, with zero-scaled terms available as padding. -/
def AtMost
    [Field K]
    (n termCount : Nat)
    (polynomial : MvPolynomial (Fin (2 * n)) K) : Prop :=
  ∃ terms : Fin termCount → SumOfTerms.Waring.Term K n,
    MvPolynomial.homogeneousComponent (2 * n) polynomial =
      ∑ index, SumOfTerms.Waring.termValue (terms index)

/-- The zero polynomial has an `r`-term decomposition for every `r`. -/
theorem zero_atMost
    [Field K]
    (n termCount : Nat) :
    AtMost n termCount (0 : MvPolynomial (Fin (2 * n)) K) := by
  let zeroTerm : SumOfTerms.Waring.Term K n :=
    { scale := 0
      coefficients := fun _ => 0 }
  refine ⟨fun _ => zeroTerm, ?_⟩
  simp [zeroTerm, SumOfTerms.Waring.termValue]

/-- Decomposition budgets add under polynomial addition. -/
theorem add
    [Field K]
    (n leftCount rightCount : Nat)
    (left right : MvPolynomial (Fin (2 * n)) K)
    (leftDecomposes : AtMost n leftCount left)
    (rightDecomposes : AtMost n rightCount right) :
    AtMost n (leftCount + rightCount) (left + right) := by
  obtain ⟨leftTerms, leftCritical⟩ := leftDecomposes
  obtain ⟨rightTerms, rightCritical⟩ := rightDecomposes
  refine ⟨Fin.addCases leftTerms rightTerms, ?_⟩
  rw [map_add, leftCritical, rightCritical, Fin.sum_univ_add]
  simp

/-- A decomposition can be padded by one zero-scaled Waring term. -/
theorem succ
    [Field K]
    (n termCount : Nat)
    (polynomial : MvPolynomial (Fin (2 * n)) K)
    (decomposes : AtMost n termCount polynomial) :
    AtMost n (termCount + 1) polynomial := by
  obtain ⟨terms, critical⟩ := decomposes
  let zeroTerm : SumOfTerms.Waring.Term K n :=
    { scale := 0
      coefficients := fun _ => 0 }
  refine ⟨Fin.lastCases zeroTerm terms, ?_⟩
  rw [critical, Fin.sum_univ_castSucc]
  simp [zeroTerm, SumOfTerms.Waring.termValue]

/-- One critical-layer Waring term gives a one-term decomposition. -/
theorem atMost_one_of_term
    [Field K]
    (n : Nat)
    (polynomial : MvPolynomial (Fin (2 * n)) K)
    (term : SumOfTerms.Waring.Term K n)
    (critical : MvPolynomial.homogeneousComponent (2 * n) polynomial =
      SumOfTerms.Waring.termValue term) :
    AtMost n 1 polynomial := by
  refine ⟨fun _ => term, ?_⟩
  simpa using critical

/-- The earlier zero-or-one-power restriction is a one-term decomposition. -/
theorem atMost_one_of_criticalLayerOrPower
    [Field K]
    (n : Nat)
    (polynomial : MvPolynomial (Fin (2 * n)) K)
    (restricted :
      MvPolynomial.homogeneousComponent (2 * n) polynomial = 0 ∨
        ∃ term : SumOfTerms.Waring.Term K n,
          MvPolynomial.homogeneousComponent (2 * n) polynomial =
            SumOfTerms.Waring.termValue term) :
    AtMost n 1 polynomial := by
  rcases restricted with invisible | ⟨term, critical⟩
  · let zeroTerm : SumOfTerms.Waring.Term K n :=
      { scale := 0
        coefficients := fun _ => 0 }
    apply atMost_one_of_term n polynomial zeroTerm
    rw [invisible]
    simp [zeroTerm, SumOfTerms.Waring.termValue]
  · exact atMost_one_of_term n polynomial term critical

/-- An `r`-term critical-layer decomposition has catalecticant rank at most
`r`. -/
theorem feature_rank_le
    [Field K]
    [CharZero K]
    (n termCount : Nat)
    (polynomial : MvPolynomial (Fin (2 * n)) K)
    (decomposes : AtMost n termCount polynomial) :
    LinearMap.rank (SumOfTerms.Waring.feature K n polynomial) ≤ termCount := by
  obtain ⟨terms, critical⟩ := decomposes
  rw [← Degree.feature_homogeneousComponent n polynomial, critical,
    map_sum]
  calc
    LinearMap.rank
        (∑ index, SumOfTerms.Waring.feature K n
          (SumOfTerms.Waring.termValue (terms index))) ≤
      ∑ index, LinearMap.rank
        (SumOfTerms.Waring.feature K n
          (SumOfTerms.Waring.termValue (terms index))) := by
        simpa using LinearMap.rank_finsetSum_le
          (Finset.univ : Finset (Fin termCount))
          (fun index => SumOfTerms.Waring.feature K n
            (SumOfTerms.Waring.termValue (terms index)))
    _ ≤ ∑ _index : Fin termCount, (1 : Cardinal) := by
      apply Finset.sum_le_sum
      intro index _
      exact SumOfTerms.Waring.term_rank_le_one (terms index)
    _ = termCount := by simp

/-- A linear-map interaction is explicitly a sum of `termCount`
catalecticant features of Waring terms. -/
def FeatureAtMost
    [Field K]
    (n termCount : Nat)
    (interaction :
      (SumOfTerms.MatrixRank.Layer (2 * n) n → K) →ₗ[K]
        (SumOfTerms.MatrixRank.Layer (2 * n) n → K)) : Prop :=
  ∃ terms : Fin termCount → SumOfTerms.Waring.Term K n,
    interaction = ∑ index,
      SumOfTerms.Waring.feature K n
        (SumOfTerms.Waring.termValue (terms index))

/-- A polynomial critical-layer decomposition induces the corresponding
feature decomposition. -/
theorem featureAtMost_of_atMost
    [Field K]
    (n termCount : Nat)
    (polynomial : MvPolynomial (Fin (2 * n)) K)
    (decomposes : AtMost n termCount polynomial) :
    FeatureAtMost n termCount (SumOfTerms.Waring.feature K n polynomial) := by
  obtain ⟨terms, critical⟩ := decomposes
  refine ⟨terms, ?_⟩
  rw [← Degree.feature_homogeneousComponent n polynomial, critical, map_sum]

/-- A feature decomposition by `r` Waring terms has rank at most `r`. -/
theorem featureDecomposition_rank_le
    [Field K]
    [CharZero K]
    (n termCount : Nat)
    (interaction :
      (SumOfTerms.MatrixRank.Layer (2 * n) n → K) →ₗ[K]
        (SumOfTerms.MatrixRank.Layer (2 * n) n → K))
    (decomposes : FeatureAtMost n termCount interaction) :
    LinearMap.rank interaction ≤ termCount := by
  obtain ⟨terms, decomposition⟩ := decomposes
  rw [decomposition]
  calc
    LinearMap.rank
        (∑ index, SumOfTerms.Waring.feature K n
          (SumOfTerms.Waring.termValue (terms index))) ≤
      ∑ index, LinearMap.rank
        (SumOfTerms.Waring.feature K n
          (SumOfTerms.Waring.termValue (terms index))) := by
        simpa using LinearMap.rank_finsetSum_le
          (Finset.univ : Finset (Fin termCount))
          (fun index => SumOfTerms.Waring.feature K n
            (SumOfTerms.Waring.termValue (terms index)))
    _ ≤ ∑ _index : Fin termCount, (1 : Cardinal) := by
      apply Finset.sum_le_sum
      intro index _
      exact SumOfTerms.Waring.term_rank_le_one (terms index)
    _ = termCount := by simp

/-- Evaluated multiplication-gate occurrences for the squarefree
catalecticant problem. -/
def multiplicationOccurrences
    [Field K]
    (constant : C → K)
    (n : Nat)
    (circuit : Circuit (Algebraic.Arithmetic.signature C) (2 * n) g 1) :
    List (Fin 2 → MvPolynomial (Fin (2 * n)) K) :=
  circuitMultiplicationArguments
    (fun scalar => MvPolynomial.C (constant scalar))
    (MvPolynomial.X : Fin (2 * n) →
      MvPolynomial (Fin (2 * n)) K)
    circuit

/-- The specialized occurrence list has exactly the circuit's multiplication
cost. -/
@[simp] theorem multiplicationOccurrences_length
    [Field K]
    (constant : C → K)
    (n : Nat)
    (circuit : Circuit (Algebraic.Arithmetic.signature C) (2 * n) g 1) :
    (multiplicationOccurrences constant n circuit).length =
      circuit.cost
        (Algebraic.Arithmetic.multiplicationCost (K := C)) :=
  circuitMultiplicationArguments_length
    (fun scalar => MvPolynomial.C (constant scalar))
    (MvPolynomial.X : Fin (2 * n) →
      MvPolynomial (Fin (2 * n)) K)
    circuit

/-- A possibly different Waring-decomposition budget for every multiplication
gate occurrence.  Equal semantic products at distinct gates retain distinct
indices and may receive different budgets. -/
def AtOccurrences
    [Field K]
    (constant : C → K)
    (n : Nat)
    (circuit : Circuit (Algebraic.Arithmetic.signature C) (2 * n) g 1)
    (budget : Fin (multiplicationOccurrences constant n circuit).length → Nat) :
    Prop :=
  ∀ index,
    let arguments := (multiplicationOccurrences constant n circuit).get index
    AtMost n (budget index)
      (arguments (0 : Fin 2) * arguments (1 : Fin 2))

/-- A semantic Waring budget depending on multiplication arguments.  Its list
sum still charges repeated occurrences separately. -/
def ArgumentAtMost
    [Field K]
    (constant : C → K)
    (n : Nat)
    (circuit : Circuit (Algebraic.Arithmetic.signature C) (2 * n) g 1)
    (budget :
      (Fin 2 → MvPolynomial (Fin (2 * n)) K) → Nat) : Prop :=
  ∀ arguments,
    arguments ∈ multiplicationOccurrences constant n circuit →
    AtMost n (budget arguments)
      (arguments (0 : Fin 2) * arguments (1 : Fin 2))

/-- Occurrence-local Waring decompositions induce the generic
occurrence-indexed rank budget. -/
theorem occurrenceIndexedBound_of_atOccurrences
    [Field K]
    [CharZero K]
    (constant : C → K)
    (n : Nat)
    (positive : 0 < n)
    (circuit : Circuit (Algebraic.Arithmetic.signature C) (2 * n) g 1)
    (budget : Fin (multiplicationOccurrences constant n circuit).length → Nat)
    (restricted : AtOccurrences constant n circuit budget) :
    Rank.Occurrence.IndexedBound (certificate constant n positive) circuit
      budget := by
  intro index
  change LinearMap.rank (SumOfTerms.Waring.feature K n
    (((multiplicationOccurrences constant n circuit).get index) (0 : Fin 2) *
      ((multiplicationOccurrences constant n circuit).get index)
        (1 : Fin 2))) ≤ budget index
  exact feature_rank_le n (budget index) _ (restricted index)

/-- Semantic argument-local Waring decompositions induce the generic
argument-dependent rank budget. -/
theorem argumentBound_of_argumentAtMost
    [Field K]
    [CharZero K]
    (constant : C → K)
    (n : Nat)
    (positive : 0 < n)
    (circuit : Circuit (Algebraic.Arithmetic.signature C) (2 * n) g 1)
    (budget :
      (Fin 2 → MvPolynomial (Fin (2 * n)) K) → Nat)
    (restricted : ArgumentAtMost constant n circuit budget) :
    Rank.Occurrence.ArgumentBound (certificate constant n positive) circuit
      budget := by
  intro arguments present
  change LinearMap.rank (SumOfTerms.Waring.feature K n
    (arguments (0 : Fin 2) * arguments (1 : Fin 2))) ≤ budget arguments
  exact feature_rank_le n (budget arguments) _
    (restricted arguments (by
      simpa [multiplicationOccurrences] using present))

/-- Weighted catalecticant Fusion bound indexed directly by multiplication
gate occurrences. -/
theorem centralBinom_le_sum_occurrenceBudget
    [Field K]
    [CharZero K]
    (constant : C → K)
    (n : Nat)
    (positive : 0 < n)
    (circuit : Circuit (Algebraic.Arithmetic.signature C) (2 * n) g 1)
    (constructs : (problem K n).Constructs circuit
      (Algebraic.Arithmetic.interpretation
        (fun scalar => MvPolynomial.C (constant scalar))))
    (budget : Fin (multiplicationOccurrences constant n circuit).length → Nat)
    (restricted : AtOccurrences constant n circuit budget) :
    Nat.centralBinom n ≤ ∑ index, budget index :=
  Rank.Occurrence.targetRank_le_sum_indexedBudget
    (certificate constant n positive) (Nat.centralBinom n)
    (SumOfTerms.Waring.target_rank_ge n) circuit constructs budget
    (occurrenceIndexedBound_of_atOccurrences constant n positive circuit budget
      restricted)

/-- Concentration form of the weighted bound: some actual multiplication
gate needs at least the ceiling-average local Waring budget. -/
theorem exists_occurrence_budget_ge_centralBinom_ceilDiv
    [Field K]
    [CharZero K]
    (constant : C → K)
    (n : Nat)
    (positive : 0 < n)
    (circuit : Circuit (Algebraic.Arithmetic.signature C) (2 * n) g 1)
    (constructs : (problem K n).Constructs circuit
      (Algebraic.Arithmetic.interpretation
        (fun scalar => MvPolynomial.C (constant scalar))))
    (budget : Fin (multiplicationOccurrences constant n circuit).length → Nat)
    (restricted : AtOccurrences constant n circuit budget) :
    ∃ index,
      Nat.centralBinom n ⌈/⌉
          circuit.cost
            (Algebraic.Arithmetic.multiplicationCost (K := C)) ≤
        budget index := by
  simpa using
    Rank.Occurrence.exists_budget_ge_ceilDiv
      (Nat.centralBinom n) (Nat.centralBinom_pos n) budget
      (centralBinom_le_sum_occurrenceBudget constant n positive circuit
        constructs budget restricted)

/-- Argument-dependent weighted catalecticant bound, expressed as a list sum
over the evaluated multiplication gates. -/
theorem centralBinom_le_sum_argumentBudget
    [Field K]
    [CharZero K]
    (constant : C → K)
    (n : Nat)
    (positive : 0 < n)
    (circuit : Circuit (Algebraic.Arithmetic.signature C) (2 * n) g 1)
    (constructs : (problem K n).Constructs circuit
      (Algebraic.Arithmetic.interpretation
        (fun scalar => MvPolynomial.C (constant scalar))))
    (budget :
      (Fin 2 → MvPolynomial (Fin (2 * n)) K) → Nat)
    (restricted : ArgumentAtMost constant n circuit budget) :
    Nat.centralBinom n ≤
      ((multiplicationOccurrences constant n circuit).map budget).sum := by
  simpa [multiplicationOccurrences] using
    Rank.Occurrence.targetRank_le_sum_argumentBudget
      (certificate constant n positive) (Nat.centralBinom n)
      (SumOfTerms.Waring.target_rank_ge n) circuit constructs budget
      (argumentBound_of_argumentAtMost constant n positive circuit budget
        restricted)

/-- Nonuniform Waring-feature decomposition budget for the actual retained
interaction occurrences of one evaluated circuit. -/
def IndexedAtMost
    [Field K]
    (constant : C → K)
    (n : Nat)
    (positive : 0 < n)
    (circuit : Circuit (Algebraic.Arithmetic.signature C) (2 * n) g 1)
    (budget : Fin (interactions (certificate constant n positive)
      (circuitAtoms circuit
        (Algebraic.Arithmetic.interpretation
          (fun scalar => MvPolynomial.C (constant scalar)))
        (MvPolynomial.X : Fin (2 * n) →
          MvPolynomial (Fin (2 * n)) K))).length → Nat) : Prop :=
  ∀ index,
    FeatureAtMost n (budget index)
      ((interactions (certificate constant n positive)
        (circuitAtoms circuit
          (Algebraic.Arithmetic.interpretation
            (fun scalar => MvPolynomial.C (constant scalar)))
          (MvPolynomial.X : Fin (2 * n) →
            MvPolynomial (Fin (2 * n)) K))).get index)

/-- Indexed Waring-feature decompositions imply the generic indexed rank
budget. -/
theorem indexedBound_of_indexedAtMost
    [Field K]
    [CharZero K]
    (constant : C → K)
    (n : Nat)
    (positive : 0 < n)
    (circuit : Circuit (Algebraic.Arithmetic.signature C) (2 * n) g 1)
    (budget : Fin (interactions (certificate constant n positive)
      (circuitAtoms circuit
        (Algebraic.Arithmetic.interpretation
          (fun scalar => MvPolynomial.C (constant scalar)))
        (MvPolynomial.X : Fin (2 * n) →
          MvPolynomial (Fin (2 * n)) K))).length → Nat)
    (decomposes : IndexedAtMost constant n positive circuit budget) :
    Rank.Local.IndexedBound (certificate constant n positive) circuit budget := by
  intro index
  exact featureDecomposition_rank_le n (budget index) _ (decomposes index)

/-- Weighted nonuniform Fusion lower bound: the total local Waring
decomposition budget across multiplication occurrences is at least the
central binomial coefficient. -/
theorem centralBinom_le_sum_indexedBudget
    [Field K]
    [CharZero K]
    (constant : C → K)
    (n : Nat)
    (positive : 0 < n)
    (circuit : Circuit (Algebraic.Arithmetic.signature C) (2 * n) g 1)
    (constructs : (problem K n).Constructs circuit
      (Algebraic.Arithmetic.interpretation
        (fun scalar => MvPolynomial.C (constant scalar))))
    (budget : Fin (interactions (certificate constant n positive)
      (circuitAtoms circuit
        (Algebraic.Arithmetic.interpretation
          (fun scalar => MvPolynomial.C (constant scalar)))
        (MvPolynomial.X : Fin (2 * n) →
          MvPolynomial (Fin (2 * n)) K))).length → Nat)
    (decomposes : IndexedAtMost constant n positive circuit budget) :
    Nat.centralBinom n ≤ ∑ index, budget index :=
  Rank.Local.targetRank_le_sum_indexedBudget
    (certificate constant n positive) (Nat.centralBinom n)
    (SumOfTerms.Waring.target_rank_ge n) circuit constructs budget
      (indexedBound_of_indexedAtMost constant n positive circuit budget
        decomposes)

/-- Circuit-local decomposition predicate for every multiplication output. -/
def AtMultiplications
    [Field K]
    (constant : C → K)
    (n : Nat)
    (circuit : Circuit (Algebraic.Arithmetic.signature C) (2 * n) g 1)
    (termCount : Nat) : Prop :=
  ∀ arguments : Fin 2 → MvPolynomial (Fin (2 * n)) K,
    (⟨.mul, arguments⟩ : Atom (Algebraic.Arithmetic.signature C)
      (MvPolynomial (Fin (2 * n)) K)) ∈
        circuitAtoms circuit
          (Algebraic.Arithmetic.interpretation
            (fun scalar => MvPolynomial.C (constant scalar)))
          (MvPolynomial.X : Fin (2 * n) →
            MvPolynomial (Fin (2 * n)) K) →
    AtMost n termCount
      (arguments (0 : Fin 2) * arguments (1 : Fin 2))

/-- A uniform atom-level restriction yields the corresponding constant
per-occurrence budget. -/
theorem atOccurrences_const_of_atMultiplications
    [Field K]
    (constant : C → K)
    (n : Nat)
    (circuit : Circuit (Algebraic.Arithmetic.signature C) (2 * n) g 1)
    (termCount : Nat)
    (restricted : AtMultiplications constant n circuit termCount) :
    AtOccurrences constant n circuit (fun _ => termCount) := by
  intro index
  let arguments := (multiplicationOccurrences constant n circuit).get index
  apply restricted arguments
  apply (mem_multiplicationArguments arguments _).mp
  simp [arguments, multiplicationOccurrences, circuitMultiplicationArguments]

/-- The same uniform restriction yields a constant semantic argument budget. -/
theorem argumentAtMost_const_of_atMultiplications
    [Field K]
    (constant : C → K)
    (n : Nat)
    (circuit : Circuit (Algebraic.Arithmetic.signature C) (2 * n) g 1)
    (termCount : Nat)
    (restricted : AtMultiplications constant n circuit termCount) :
    ArgumentAtMost constant n circuit (fun _ => termCount) := by
  intro arguments present
  apply restricted arguments
  apply (mem_multiplicationArguments arguments _).mp
  simpa [multiplicationOccurrences, circuitMultiplicationArguments] using present

/-- Local `r`-term decompositions imply the atom-level catalecticant rank
bound `r`. -/
theorem multiplicationOutputRankAtMost_of_atMultiplications
    [Field K]
    [CharZero K]
    (constant : C → K)
    (n : Nat)
    (positive : 0 < n)
    (circuit : Circuit (Algebraic.Arithmetic.signature C) (2 * n) g 1)
    (termCount : Nat)
    (restricted : AtMultiplications constant n circuit termCount) :
    MultiplicationOutputRankAtMost constant n positive circuit termCount := by
  intro arguments present
  change LinearMap.rank
    (SumOfTerms.Waring.feature K n
      (arguments (0 : Fin 2) * arguments (1 : Fin 2))) ≤ termCount
  exact feature_rank_le n termCount _ (restricted arguments present)

/-- Locally `r`-decomposable critical layers force the central-binomial
rank/cost tradeoff. -/
theorem centralBinom_ceilDiv_lowerBound
    [Field K]
    [CharZero K]
    (constant : C → K)
    (n : Nat)
    (positive : 0 < n)
    (termCount : Nat)
    (termCountPositive : 0 < termCount)
    (circuit : Circuit (Algebraic.Arithmetic.signature C) (2 * n) g 1)
    (constructs : (problem K n).Constructs circuit
      (Algebraic.Arithmetic.interpretation
        (fun scalar => MvPolynomial.C (constant scalar))))
    (restricted : AtMultiplications constant n circuit termCount) :
    Nat.centralBinom n ⌈/⌉ termCount ≤
      circuit.cost
        (Algebraic.Arithmetic.multiplicationCost (K := C)) :=
  Catalecticant.centralBinom_ceilDiv_lowerBound constant n positive termCount
    termCountPositive circuit constructs
      (localRankAtMost_of_multiplicationOutputRankAtMost constant n positive
        circuit termCount
          (multiplicationOutputRankAtMost_of_atMultiplications constant n
            positive circuit termCount restricted))

/-- Undivided form of the locally decomposable critical-layer tradeoff. -/
theorem centralBinom_le_cost_mul_termCount
    [Field K]
    [CharZero K]
    (constant : C → K)
    (n : Nat)
    (positive : 0 < n)
    (termCount : Nat)
    (circuit : Circuit (Algebraic.Arithmetic.signature C) (2 * n) g 1)
    (constructs : (problem K n).Constructs circuit
      (Algebraic.Arithmetic.interpretation
        (fun scalar => MvPolynomial.C (constant scalar))))
    (restricted : AtMultiplications constant n circuit termCount) :
    Nat.centralBinom n ≤
      circuit.cost
          (Algebraic.Arithmetic.multiplicationCost (K := C)) *
        termCount :=
  centralBinom_le_cost_mul_rank constant n positive termCount circuit constructs
    (localRankAtMost_of_multiplicationOutputRankAtMost constant n positive
      circuit termCount
        (multiplicationOutputRankAtMost_of_atMultiplications constant n positive
          circuit termCount restricted))

end
end Decomposition
end Catalecticant
end Polynomial
end Interaction
end Arithmetic
end Fusion
end Algebraic
