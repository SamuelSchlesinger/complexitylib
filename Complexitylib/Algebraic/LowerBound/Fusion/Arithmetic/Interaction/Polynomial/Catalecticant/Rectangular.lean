/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Fusion.Arithmetic.Interaction.Rank.Local
public import Complexitylib.Algebraic.LowerBound.Fusion.Arithmetic.Interaction.Linear
public import Complexitylib.Algebraic.LowerBound.Fusion.SumOfTerms.Waring.Rectangular

/-!
# Rectangular catalecticant Fusion for ordinary arithmetic circuits

Lift the degree/split-parametric Waring flattening to ordinary arithmetic
circuits.  For total degree `d ≥ 2`, constants and input variables are
invisible.  A local interaction-rank bound `r` therefore yields

`ceil(choose d k / r) ≤ multiplication cost`.
-/

@[expose] public section

namespace Algebraic
namespace Fusion
namespace Arithmetic
namespace Interaction
namespace Polynomial
namespace Catalecticant
namespace Rectangular

noncomputable section

open Cardinal

variable {K : Type} {C : Type}

/-- Queried degree-`d` exponents are nonzero when `d` is positive. -/
theorem entryExponent_ne_zero
    (degree split : Nat)
    (positive : 0 < degree)
    (row column : SumOfTerms.MatrixRank.Layer degree split) :
    SumOfTerms.Waring.Rectangular.entryExponent degree split row column ≠ 0 := by
  intro equal
  have sumEqual := congrArg
    (fun exponent : Fin degree →₀ Nat =>
      exponent.sum (fun _ multiplicity => multiplicity)) equal
  rw [SumOfTerms.Waring.Rectangular.entryExponent_sum] at sumEqual
  simp at sumEqual
  omega

/-- Queried degree-`d` exponents are not degree-one input exponents when
`d ≥ 2`. -/
theorem entryExponent_ne_single
    (degree split : Nat)
    (degreeAtLeastTwo : 2 ≤ degree)
    (row column : SumOfTerms.MatrixRank.Layer degree split)
    (input : Fin degree) :
    SumOfTerms.Waring.Rectangular.entryExponent degree split row column ≠
      Finsupp.single input 1 := by
  intro equal
  have sumEqual := congrArg
    (fun exponent : Fin degree →₀ Nat =>
      exponent.sum (fun _ multiplicity => multiplicity)) equal
  rw [SumOfTerms.Waring.Rectangular.entryExponent_sum] at sumEqual
  simp at sumEqual
  omega

/-- Constants have zero rectangular catalecticant. -/
theorem catalecticant_C_eq_zero
    [Field K]
    (degree split : Nat)
    (positive : 0 < degree)
    (scalar : K) :
    SumOfTerms.Waring.Rectangular.catalecticant K degree split
      (MvPolynomial.C scalar) = 0 := by
  classical
  ext row column
  simp [SumOfTerms.Waring.Rectangular.catalecticant_apply, MvPolynomial.coeff_C,
    (entryExponent_ne_zero degree split positive row column).symm]

/-- Input variables have zero rectangular catalecticant in degree at least
two. -/
theorem catalecticant_X_eq_zero
    [Field K]
    (degree split : Nat)
    (degreeAtLeastTwo : 2 ≤ degree)
    (input : Fin degree) :
    SumOfTerms.Waring.Rectangular.catalecticant K degree split
      (MvPolynomial.X input) = 0 := by
  classical
  ext row column
  simp [SumOfTerms.Waring.Rectangular.catalecticant_apply, MvPolynomial.coeff_X,
    (entryExponent_ne_single degree split degreeAtLeastTwo row column
      input).symm]

theorem feature_C_eq_zero
    [Field K]
    (degree split : Nat)
    (positive : 0 < degree)
    (scalar : K) :
    SumOfTerms.Waring.Rectangular.feature K degree split (MvPolynomial.C scalar) = 0 := by
  simp [SumOfTerms.Waring.Rectangular.feature,
    catalecticant_C_eq_zero degree split positive scalar]

theorem feature_X_eq_zero
    [Field K]
    (degree split : Nat)
    (degreeAtLeastTwo : 2 ≤ degree)
    (input : Fin degree) :
    SumOfTerms.Waring.Rectangular.feature K degree split (MvPolynomial.X input) = 0 := by
  simp [SumOfTerms.Waring.Rectangular.feature,
    catalecticant_X_eq_zero degree split degreeAtLeastTwo input]

/-- Ordinary arithmetic problem of constructing the degree-`d` squarefree
monomial. -/
abbrev problem
    (K : Type)
    [Field K]
    (degree : Nat) : Problem (MvPolynomial (Fin degree) K) where
  inputCount := degree
  inputs := MvPolynomial.X
  target := SumOfTerms.Waring.Rectangular.target K degree

/-- Interaction certificate induced by the degree/split catalecticant. -/
def certificate
    [Field K]
    (constant : C → K)
    (degree split : Nat)
    (degreeAtLeastTwo : 2 ≤ degree) :
    Interaction.Certificate (K := K)
      (Q := (SumOfTerms.MatrixRank.Layer degree split → K) →ₗ[K]
        (SumOfTerms.MatrixRank.Layer degree split → K))
      (fun scalar => MvPolynomial.C (constant scalar))
      (problem K degree) :=
  Linear.certificate
    (fun scalar => MvPolynomial.C (constant scalar))
    (problem K degree) (SumOfTerms.Waring.Rectangular.feature K degree split)
    (fun input => feature_X_eq_zero degree split degreeAtLeastTwo input)
    (fun scalar => feature_C_eq_zero degree split
      (by omega) (constant scalar))

/-- Local rank restriction on the actual multiplication interactions. -/
def LocalRankAtMost
    [Field K]
    (constant : C → K)
    (degree split : Nat)
    (degreeAtLeastTwo : 2 ≤ degree)
    (circuit : Circuit (Algebraic.Arithmetic.signature C) degree 1)
    (interactionRank : Nat) : Prop :=
  Rank.Local.CircuitBound
    (certificate constant degree split degreeAtLeastTwo) circuit interactionRank

/-- Atom-level local rank restriction. -/
def MultiplicationOutputRankAtMost
    [Field K]
    (constant : C → K)
    (degree split : Nat)
    (degreeAtLeastTwo : 2 ≤ degree)
    (circuit : Circuit (Algebraic.Arithmetic.signature C) degree 1)
    (interactionRank : Nat) : Prop :=
  Rank.Local.MultiplicationBound
    (certificate constant degree split degreeAtLeastTwo) circuit interactionRank

theorem localRankAtMost_of_multiplicationOutputRankAtMost
    [Field K]
    (constant : C → K)
    (degree split : Nat)
    (degreeAtLeastTwo : 2 ≤ degree)
    (circuit : Circuit (Algebraic.Arithmetic.signature C) degree 1)
    (interactionRank : Nat)
    (bound : MultiplicationOutputRankAtMost constant degree split
      degreeAtLeastTwo circuit interactionRank) :
    LocalRankAtMost constant degree split degreeAtLeastTwo circuit
      interactionRank :=
  Rank.Local.CircuitBound.of_multiplicationBound
    (certificate constant degree split degreeAtLeastTwo) circuit
      interactionRank bound

/-- General rectangular local-rank tradeoff. -/
theorem choose_ceilDiv_lowerBound
    [Field K]
    [CharZero K]
    (constant : C → K)
    (degree split : Nat)
    (degreeAtLeastTwo : 2 ≤ degree)
    (interactionRank : Nat)
    (rankPositive : 0 < interactionRank)
    (circuit : Circuit (Algebraic.Arithmetic.signature C) degree 1)
    (constructs : (problem K degree).Constructs circuit
      (Algebraic.Arithmetic.interpretation
        (fun scalar => MvPolynomial.C (constant scalar))))
    (localBound : LocalRankAtMost constant degree split degreeAtLeastTwo
      circuit interactionRank) :
    Nat.choose degree split ⌈/⌉ interactionRank ≤
      circuit.cost
        (Algebraic.Arithmetic.multiplicationCost (K := C)) := by
  apply Rank.Local.circuit_lowerBound
    (certificate constant degree split degreeAtLeastTwo)
    (Nat.choose degree split) interactionRank
  · exact SumOfTerms.Waring.Rectangular.target_rank_ge degree split
  · exact rankPositive
  · exact constructs
  · exact localBound

/-- Undivided rectangular rank/cost tradeoff. -/
theorem choose_le_cost_mul_rank
    [Field K]
    [CharZero K]
    (constant : C → K)
    (degree split : Nat)
    (degreeAtLeastTwo : 2 ≤ degree)
    (interactionRank : Nat)
    (circuit : Circuit (Algebraic.Arithmetic.signature C) degree 1)
    (constructs : (problem K degree).Constructs circuit
      (Algebraic.Arithmetic.interpretation
        (fun scalar => MvPolynomial.C (constant scalar))))
    (localBound : LocalRankAtMost constant degree split degreeAtLeastTwo
      circuit interactionRank) :
    Nat.choose degree split ≤
      circuit.cost
          (Algebraic.Arithmetic.multiplicationCost (K := C)) *
        interactionRank :=
  Rank.Local.targetRank_le_mul_multiplicationCost
    (certificate constant degree split degreeAtLeastTwo)
    (Nat.choose degree split) interactionRank
    (SumOfTerms.Waring.Rectangular.target_rank_ge degree split)
    circuit constructs localBound

/-- Rank-one multiplication outputs force the full layer-size lower bound. -/
theorem rankOne_multiplication_lowerBound
    [Field K]
    [CharZero K]
    (constant : C → K)
    (degree split : Nat)
    (degreeAtLeastTwo : 2 ≤ degree)
    (circuit : Circuit (Algebraic.Arithmetic.signature C) degree 1)
    (constructs : (problem K degree).Constructs circuit
      (Algebraic.Arithmetic.interpretation
        (fun scalar => MvPolynomial.C (constant scalar))))
    (localBound : LocalRankAtMost constant degree split degreeAtLeastTwo
      circuit 1) :
    Nat.choose degree split ≤
      circuit.cost
        (Algebraic.Arithmetic.multiplicationCost (K := C)) := by
  simpa using choose_ceilDiv_lowerBound constant degree split degreeAtLeastTwo
    1 (by simp) circuit constructs localBound

/-- Concrete subclass: every multiplication output is invisible or a single
degree-`d` Waring term. -/
def PowerOrInvisibleAtMultiplications
    [Field K]
    (constant : C → K)
    (degree split : Nat)
    (circuit : Circuit (Algebraic.Arithmetic.signature C) degree 1) : Prop :=
  ∀ arguments : Fin 2 → MvPolynomial (Fin degree) K,
    (⟨.mul, arguments⟩ : Atom (Algebraic.Arithmetic.signature C)
      (MvPolynomial (Fin degree) K)) ∈
        circuitAtoms circuit
          (Algebraic.Arithmetic.interpretation
            (fun scalar => MvPolynomial.C (constant scalar)))
          (MvPolynomial.X : Fin degree → MvPolynomial (Fin degree) K) →
    SumOfTerms.Waring.Rectangular.feature K degree split
        (arguments (0 : Fin 2) * arguments (1 : Fin 2)) = 0 ∨
      ∃ term : SumOfTerms.Waring.Rectangular.Term K degree,
        arguments (0 : Fin 2) * arguments (1 : Fin 2) =
          SumOfTerms.Waring.Rectangular.termValue term

theorem multiplicationOutputRankAtMost_one_of_powerOrInvisible
    [Field K]
    [CharZero K]
    (constant : C → K)
    (degree split : Nat)
    (degreeAtLeastTwo : 2 ≤ degree)
    (circuit : Circuit (Algebraic.Arithmetic.signature C) degree 1)
    (restricted : PowerOrInvisibleAtMultiplications constant degree split
      circuit) :
    MultiplicationOutputRankAtMost constant degree split degreeAtLeastTwo
      circuit 1 := by
  intro arguments present
  change LinearMap.rank
    (SumOfTerms.Waring.Rectangular.feature K degree split
      (arguments (0 : Fin 2) * arguments (1 : Fin 2))) ≤ 1
  rcases restricted arguments present with invisible | ⟨term, powerTerm⟩
  · rw [invisible]
    simp
  · rw [powerTerm]
    exact SumOfTerms.Waring.Rectangular.term_rank_le_one term split

/-- Power-or-invisible circuits inherit the binomial multiplication lower
bound. -/
theorem powerOrInvisible_multiplication_lowerBound
    [Field K]
    [CharZero K]
    (constant : C → K)
    (degree split : Nat)
    (degreeAtLeastTwo : 2 ≤ degree)
    (circuit : Circuit (Algebraic.Arithmetic.signature C) degree 1)
    (constructs : (problem K degree).Constructs circuit
      (Algebraic.Arithmetic.interpretation
        (fun scalar => MvPolynomial.C (constant scalar))))
    (restricted : PowerOrInvisibleAtMultiplications constant degree split
      circuit) :
    Nat.choose degree split ≤
      circuit.cost
        (Algebraic.Arithmetic.multiplicationCost (K := C)) :=
  rankOne_multiplication_lowerBound constant degree split degreeAtLeastTwo
    circuit constructs
    (localRankAtMost_of_multiplicationOutputRankAtMost constant degree split
      degreeAtLeastTwo circuit 1
      (multiplicationOutputRankAtMost_one_of_powerOrInvisible constant degree
        split degreeAtLeastTwo circuit restricted))

end
end Rectangular
end Catalecticant
end Polynomial
end Interaction
end Arithmetic
end Fusion
end Algebraic
