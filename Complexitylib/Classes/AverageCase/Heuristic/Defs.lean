/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Classes.AverageCase.FiniteEnsemble.Defs
public import Complexitylib.Classes.P.Defs

/-!
# Errorless average-case heuristics -- definitions

An errorless heuristic answers yes, answers no, or explicitly fails. It may fail
on any input but may never return an incorrect Boolean answer. Average-case
complexity bounds the probability of the failure event under a distribution
ensemble.

The canonical answer codec uses `[]` for failure, `[false]` for rejection, and
`[true]` for acceptance. Consequently, polynomial runtime is stated directly as
membership of the encoded answer function in the existing class `FP`.
-/


@[expose] public section

namespace Complexity

/-- The three possible outputs of an errorless heuristic. -/
inductive HeuristicAnswer where
  /-- Certified yes answer. -/
  | accept
  /-- Certified no answer. -/
  | reject
  /-- Explicit failure to answer. -/
  | failure
  deriving Repr, DecidableEq

namespace HeuristicAnswer

/-- Canonical output encoding: one Boolean bit for an answer, empty for
failure. -/
def encode : HeuristicAnswer → List Bool
  | .accept => [true]
  | .reject => [false]
  | .failure => []

/-- Decode one canonical errorless-heuristic answer, rejecting every string of
length at least two. -/
def decode? : List Bool → Option HeuristicAnswer
  | [] => some .failure
  | [true] => some .accept
  | [false] => some .reject
  | _ => none

/-- Swap yes and no while preserving failure. -/
def complement : HeuristicAnswer → HeuristicAnswer
  | .accept => .reject
  | .reject => .accept
  | .failure => .failure

/-- An answer is sound for a proposition. Failure is always sound; the other
two cases assert the corresponding truth value. -/
def CorrectFor (answer : HeuristicAnswer) (truth : Prop) : Prop :=
  match answer with
  | .accept => truth
  | .reject => ¬ truth
  | .failure => True

end HeuristicAnswer

/-- A deterministic semantic heuristic before its efficiency and correctness
properties are imposed. -/
abbrev HeuristicAlgorithm := List Bool → HeuristicAnswer

namespace HeuristicAlgorithm

/-- Canonical binary output function computed by a heuristic. -/
def encoded (A : HeuristicAlgorithm) : List Bool → List Bool :=
  fun x => (A x).encode

/-- A heuristic runs in deterministic polynomial time when its canonical
three-answer encoding belongs to `FP`. -/
def IsPolynomialTime (A : HeuristicAlgorithm) : Prop :=
  A.encoded ∈ FP

/-- An errorless heuristic never returns an incorrect answer for `L`. -/
def IsErrorlessFor (A : HeuristicAlgorithm) (L : Language) : Prop :=
  ∀ x, (A x).CorrectFor (x ∈ L)

/-- Complement a heuristic pointwise, swapping acceptance and rejection. -/
def complement (A : HeuristicAlgorithm) : HeuristicAlgorithm :=
  fun x => (A x).complement

/-- Turn a total Boolean decision function into a never-failing heuristic. -/
def ofDecision (decide : List Bool → Bool) : HeuristicAlgorithm :=
  fun x => if decide x then .accept else .reject

/-- Exact probability of one answer on one ensemble slice. -/
def answerProbability (D : FiniteEnsemble (List Bool))
    (A : HeuristicAlgorithm) (answer : HeuristicAnswer) (n : ℕ) : ℚ :=
  D.probability n fun x => A x = answer

/-- Exact failure probability of a heuristic on one ensemble slice. -/
def failureProbability (D : FiniteEnsemble (List Bool))
    (A : HeuristicAlgorithm) (n : ℕ) : ℚ :=
  D.probability n fun x => A x = .failure

/-- Pointwise failure-probability bound across every ensemble slice. -/
def FailsWithProbabilityAtMost (D : FiniteEnsemble (List Bool))
    (A : HeuristicAlgorithm) (δ : ℕ → ℚ) : Prop :=
  ∀ n, A.failureProbability D n ≤ δ n

end HeuristicAlgorithm

namespace FiniteEnsemble

/-- Exact mass assigned to a language on one ensemble slice. Classical
decidability is confined to this finite semantic enumeration. -/
noncomputable def languageProbability (D : FiniteEnsemble (List Bool))
    (L : Language) (n : ℕ) : ℚ := by
  classical
  exact D.probability n fun x => x ∈ L

end FiniteEnsemble

/-- A language together with a parameterized input distribution. No complexity
or samplability condition is imposed by the structure itself. -/
structure DistributionalProblem where
  /-- Decision problem being solved. -/
  language : Language
  /-- Distribution ensemble on inputs. -/
  ensemble : FiniteEnsemble (List Bool)

namespace DistributionalProblem

/-- Complement the language while retaining exactly the same input ensemble. -/
def complement (problem : DistributionalProblem) : DistributionalProblem where
  language := problem.languageᶜ
  ensemble := problem.ensemble

end DistributionalProblem

/-- Distributional problems admitting a deterministic polynomial-time
errorless heuristic with failure bounded by `δ` on every slice. -/
def AvgPAt (δ : ℕ → ℚ) : Set DistributionalProblem :=
  {problem | ∃ A : HeuristicAlgorithm,
    A.IsPolynomialTime ∧
      A.IsErrorlessFor problem.language ∧
      A.FailsWithProbabilityAtMost problem.ensemble δ}

/-- Total inverse-polynomial failure bound. It agrees with `n⁻ᶜ` for positive
`n` and assigns the harmless bound one to the zero slice. -/
def inversePolynomialFailure (c n : ℕ) : ℚ :=
  1 / (Nat.max 1 n : ℚ) ^ c

/-- Errorless average-case polynomial time: for every inverse-polynomial
failure target, a polynomial-time errorless heuristic meets that target.

The heuristic never sees the slice index `n`, and its time is polynomial in the
sample length `|x|`. A `FiniteEnsemble` may draw samples much shorter than `n`,
and then this is stricter than the textbook time bound polynomial in `n`; a
future `DistNP` should require samples of length polynomially related to `n`. -/
def AvgP : Set DistributionalProblem :=
  ⋂ c : ℕ, AvgPAt (inversePolynomialFailure c)

end Complexity
