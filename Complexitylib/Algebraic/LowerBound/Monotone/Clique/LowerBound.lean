/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Monotone.Clique.Negative

/-!
# A parameterized monotone CLIQUE circuit lower bound

This file combines the positive truncation scheme and the negative plucking
scheme.  Both evaluate the same bounded-width approximator on the shared DAG,
so a small positive-error budget forces the final family to be nonempty while
the negative density lemma forces that same family to make many errors.

The main result is an explicit, division-free dichotomy.  It is useful both
for exact finite parameter choices and for later asymptotic specialization.
-/

@[expose] public section

namespace Algebraic
namespace Monotone
namespace Clique
namespace LowerBound

noncomputable section

open Approx

/-- Uniform positive error cap per circuit gate. -/
abbrev positiveGateCap
    (n k petalCount width : Nat) : Nat :=
  Positive.errorCap n k petalCount width

/-- A common upper bound for the two negative per-operation costs. -/
def negativeGateCap
    (n r petalCount width : Nat) : Nat :=
  let familyBound := Sunflower.bound petalCount width
  (2 * familyBound + familyBound ^ 2) *
    Negative.pluckErrorCap n r petalCount width

private theorem positive_operationCost_le
    (n k petalCount width : Nat)
    (op : AndOr.Op) :
    Positive.operationCost n k petalCount width op ≤
      positiveGateCap n k petalCount width := by
  cases op <;> simp [Positive.operationCost, positiveGateCap]

private theorem negative_operationCost_le
    (n r petalCount width : Nat)
    (op : AndOr.Op) :
    Negative.operationCost n r petalCount width op ≤
      negativeGateCap n r petalCount width := by
  cases op <;>
    simp only [Negative.operationCost, negativeGateCap] <;>
    gcongr <;> omega

/-- The approximator produced at the output of a circuit. -/
def outputFamily
    (petalCount : Nat)
    (two_le_petals : 2 ≤ petalCount)
    (width : Nat)
    (two_le_width : 2 ≤ width)
    (circuit : Circuit AndOr.signature (edgeCount n) 1) :
    NormalFamily n petalCount width :=
  circuit.eval
    (normalInterpretation petalCount two_le_petals width)
    (normalInput petalCount width two_le_petals two_le_width) 0

/-- If the positive local-error budget is smaller than the number of minimal
positive clique graphs, the output approximator contains a term. -/
theorem outputFamily_nonempty
    (n k petalCount width : Nat)
    (two_le_petals : 2 ≤ petalCount)
    (two_le_width : 2 ≤ width)
    (width_succ_le_k : width + 1 ≤ k)
    (circuit : Circuit AndOr.signature (edgeCount n) 1)
    (computes : ∀ assignment,
      circuit.eval AndOr.boolInterpretation assignment 0 =
        function n k assignment)
    (budgetSmall : positiveGateCap n k petalCount width * circuit.size <
      Nat.choose n k) :
    (outputFamily petalCount two_le_petals width two_le_width
      circuit).family.Nonempty := by
  classical
  let positiveScheme := Positive.scheme n k petalCount width
    two_le_petals two_le_width width_succ_le_k
  let value := outputFamily petalCount two_le_petals width two_le_width circuit
  let failures := Approximation.Scheme.failures
    positiveScheme.relation
    (fun family clique =>
      normalDecode family (cliqueAssignment clique.1))
    value (fun _clique : CliqueSet n k => true)
  have computesPositive : ∀ clique : CliqueSet n k,
      circuit.eval AndOr.boolInterpretation
        (cliqueAssignment clique.1) 0 = true := by
    intro clique
    rw [computes]
    exact function_cliqueAssignment clique
  have failureCost : failures.card ≤
      circuit.cost positiveScheme.errorCost := by
    exact positiveScheme.failures_card_le_cost circuit
      (fun _clique : CliqueSet n k => true) computesPositive
  have costBound : circuit.cost positiveScheme.errorCost ≤
      positiveGateCap n k petalCount width * circuit.size := by
    apply circuit.cost_le_mul_size
    intro op
    exact positive_operationCost_le n k petalCount width op
  have failureSmall : failures.card < Fintype.card (CliqueSet n k) := by
    apply lt_of_le_of_lt (failureCost.trans costBound)
    simpa using budgetSmall
  obtain ⟨clique, fresh⟩ : ∃ clique : CliqueSet n k,
      clique ∉ failures := by
    by_contra none
    push Not at none
    have allFail : (Finset.univ : Finset (CliqueSet n k)) ⊆ failures :=
      fun clique _ => none clique
    have cardinality := Finset.card_le_card allFail
    rw [Finset.card_univ] at cardinality
    omega
  have related : true ≤
      normalDecode value (cliqueAssignment clique.1) := by
    by_contra disagreement
    apply fresh
    rw [Approximation.Scheme.mem_failures]
    exact disagreement
  have decodedTrue : normalDecode value (cliqueAssignment clique.1) = true :=
    Bool.eq_true_of_true_le related
  rw [normalDecode_eq_true] at decodedTrue
  obtain ⟨term, present, _⟩ := decodedTrue
  exact ⟨term, present⟩

/-- The accepted negative colorings of the circuit's output approximator are
contained in the negative scheme's global failure set. -/
theorem acceptedColorings_card_le_negativeCost
    (n k petalCount width : Nat)
    (kPositive : 0 < k)
    (two_le_petals : 2 ≤ petalCount)
    (two_le_width : 2 ≤ width)
    (circuit : Circuit AndOr.signature (edgeCount n) 1)
    (computes : ∀ assignment,
      circuit.eval AndOr.boolInterpretation assignment 0 =
        function n k assignment) :
    (Negative.acceptedColorings (k - 1)
      (outputFamily petalCount two_le_petals width two_le_width
        circuit).family).card ≤
      circuit.cost
        (Negative.operationCost n (k - 1) petalCount width) := by
  classical
  let negativeScheme := Negative.scheme n (k - 1) petalCount width
    two_le_petals two_le_width
  let value := outputFamily petalCount two_le_petals width two_le_width circuit
  let failures := Approximation.Scheme.failures
    negativeScheme.relation
    (fun family coloring =>
      normalDecode family (coloringAssignment coloring))
    value (fun _coloring : Coloring n (k - 1) => false)
  have computesNegative : ∀ coloring : Coloring n (k - 1),
      circuit.eval AndOr.boolInterpretation
        (coloringAssignment coloring) 0 = false := by
    intro coloring
    rw [computes]
    exact function_coloringAssignment_eq_false kPositive coloring
  have failureCost : failures.card ≤
      circuit.cost negativeScheme.errorCost := by
    exact negativeScheme.failures_card_le_cost circuit
      (fun _coloring : Coloring n (k - 1) => false) computesNegative
  apply (Finset.card_le_card ?_).trans failureCost
  intro coloring accepted
  rw [Negative.mem_acceptedColorings] at accepted
  rw [Approximation.Scheme.mem_failures]
  have decodedTrue : normalDecode value (coloringAssignment coloring) = true :=
    (normalDecode_eq_true value (coloringAssignment coloring)).2 accepted
  change ¬ (normalDecode value (coloringAssignment coloring) ≤ false)
  rw [decodedTrue]
  decide

/-- Razborov's bounded-width approximation dichotomy in explicit finite
form.  Every monotone circuit computing `k`-CLIQUE must exhaust either the
positive truncation budget or the negative plucking budget. -/
theorem circuitSize_dichotomy
    (n k petalCount width : Nat)
    (nPositive : 0 < n)
    (kPositive : 0 < k)
    (two_le_petals : 2 ≤ petalCount)
    (two_le_width : 2 ≤ width)
    (width_succ_le_k : width + 1 ≤ k)
    (colorsLarge : 2 * width ^ 2 ≤ k - 1)
    (circuit : Circuit AndOr.signature (edgeCount n) 1)
    (computes : ∀ assignment,
      circuit.eval AndOr.boolInterpretation assignment 0 =
        function n k assignment) :
    Nat.choose n k ≤
        positiveGateCap n k petalCount width * circuit.size ∨
      (k - 1) ^ n ≤
        2 * negativeGateCap n (k - 1) petalCount width * circuit.size := by
  by_cases positiveSpent : Nat.choose n k ≤
      positiveGateCap n k petalCount width * circuit.size
  · exact Or.inl positiveSpent
  · right
    let output := outputFamily petalCount two_le_petals width
      two_le_width circuit
    have nonempty : output.family.Nonempty :=
      outputFamily_nonempty n k petalCount width
      two_le_petals two_le_width width_succ_le_k circuit computes
      (Nat.lt_of_not_ge positiveSpent)
    have density := Negative.half_colorings_accepted nPositive (k - 1) width
      colorsLarge output.family output.bounded nonempty
    have errorBound := acceptedColorings_card_le_negativeCost
      n k petalCount width kPositive two_le_petals two_le_width circuit computes
    have costBound : circuit.cost
        (Negative.operationCost n (k - 1) petalCount width) ≤
        negativeGateCap n (k - 1) petalCount width * circuit.size := by
      apply circuit.cost_le_mul_size
      intro op
      exact negative_operationCost_le n (k - 1) petalCount width op
    exact density.trans <| (Nat.mul_le_mul_left 2
      (errorBound.trans costBound)).trans_eq (by
        simp [Nat.mul_assoc])

/-- Any size bound below both error thresholds is smaller than the circuit. -/
theorem sizeBound_lt_circuitSize
    (n k petalCount width sizeBound : Nat)
    (nPositive : 0 < n)
    (kPositive : 0 < k)
    (two_le_petals : 2 ≤ petalCount)
    (two_le_width : 2 ≤ width)
    (width_succ_le_k : width + 1 ≤ k)
    (colorsLarge : 2 * width ^ 2 ≤ k - 1)
    (positiveBudget : positiveGateCap n k petalCount width * sizeBound <
      Nat.choose n k)
    (negativeBudget :
      2 * negativeGateCap n (k - 1) petalCount width * sizeBound <
        (k - 1) ^ n)
    (circuit : Circuit AndOr.signature (edgeCount n) 1)
    (computes : ∀ assignment,
      circuit.eval AndOr.boolInterpretation assignment 0 =
        function n k assignment) :
    sizeBound < circuit.size := by
  by_contra notLarger
  have sizeLe : circuit.size ≤ sizeBound := Nat.le_of_not_gt notLarger
  rcases circuitSize_dichotomy n k petalCount width nPositive kPositive
      two_le_petals two_le_width width_succ_le_k colorsLarge circuit computes with
    positiveSpent | negativeSpent
  · have := positiveSpent.trans <|
      Nat.mul_le_mul_left _ sizeLe
    omega
  · have := negativeSpent.trans <|
      Nat.mul_le_mul_left _ sizeLe
    omega

end

end LowerBound
end Clique
end Monotone
end Algebraic
