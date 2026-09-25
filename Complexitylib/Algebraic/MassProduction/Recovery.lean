/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.MassProduction.EvaluationCode
public import Complexitylib.Algebraic.MassProduction.Scheduler

/-!
# Scheduled recovery from the low-degree resource table

This module joins the tensor-grid evaluation code to projective affine-line
scheduling. It proves the semantic local-recovery gadget from the
[Boolean mass-production manuscript](https://github.com/SamuelSchlesinger/boolean-mass-production):
every scheduled punctured line recovers its target symbol, and the greedy
schedule can make all recovery sets in one group pairwise disjoint.
-/

@[expose] public section

namespace Algebraic
namespace MassProduction

open scoped BigOperators LinearAlgebra.Projectivization

/-- Every sufficiently low-degree evaluation-code symbol is the sum over any
projective punctured line through it. -/
theorem evaluationCode_sum_puncturedLine
    {K Index Coordinate : Type*}
    [Fintype K] [Field K] [DecidableEq K] [CharP K 2]
    [Fintype Index] [DecidableEq Index]
    [Fintype Coordinate] [DecidableEq Coordinate]
    (nodes : Index -> K)
    (message : (Coordinate -> Index) -> K)
    (degree : Fintype.card Coordinate * (Fintype.card Index - 1) <
      Fintype.card K - 1)
    (target : Coordinate -> K)
    (direction : ℙ K (Coordinate -> K)) :
    evaluationCode nodes message target =
      ∑ point ∈ puncturedLine target direction,
        evaluationCode nodes message point := by
  rw [sum_puncturedLine]
  rw [evaluationCode_line_recovery_charTwo nodes message degree
    target direction.rep]
  apply Finset.sum_congr rfl
  intro scalar _
  congr 1
  funext coordinate
  simp [Pi.smul_apply, mul_comm]

/-- At the paper's canonical grid width, punctured-line recovery holds in
every positive dimension. -/
theorem paperEvaluationCode_sum_puncturedLine
    (K : Type*)
    [Fintype K] [Field K] [DecidableEq K] [CharP K 2]
    (dimension : Nat)
    (dimensionPositive : 0 < dimension)
    (message :
      (Fin dimension ->
        Fin (resourceGridWidth (Fintype.card K) dimension)) -> K)
    (target : Fin dimension -> K)
    (direction : ℙ K (Fin dimension -> K)) :
    paperEvaluationCode K dimension message target =
      ∑ point ∈ puncturedLine target direction,
        paperEvaluationCode K dimension message point := by
  unfold paperEvaluationCode
  apply evaluationCode_sum_puncturedLine
  simpa only [Fintype.card_fin] using
    resourceGridWidth_degree_lt (Fintype.card K) dimension
      Fintype.one_lt_card dimensionPositive

/-- Aligned target and direction lists recover every target code symbol. -/
theorem paperEvaluationCode_recoverySets
    (K : Type*)
    [Fintype K] [Field K] [DecidableEq K] [CharP K 2]
    (dimension : Nat)
    (dimensionPositive : 0 < dimension)
    (message :
      (Fin dimension ->
        Fin (resourceGridWidth (Fintype.card K) dimension)) -> K)
    (targets : List (Fin dimension -> K))
    (directions : List (ℙ K (Fin dimension -> K)))
    (equalLength : directions.length = targets.length) :
    (recoverySets targets directions).map
        (fun set => ∑ point ∈ set,
          paperEvaluationCode K dimension message point) =
      targets.map (paperEvaluationCode K dimension message) := by
  induction targets generalizing directions with
  | nil =>
      have directionsEmpty : directions = [] :=
        List.length_eq_zero_iff.mp equalLength
      subst directions
      rfl
  | cons target targets inductionHypothesis =>
      cases directions with
      | nil => simp at equalLength
      | cons direction directions =>
          simp only [List.length_cons, Nat.add_right_cancel_iff] at equalLength
          simp only [recoverySets, List.map_cons, List.cons.injEq]
          exact ⟨(paperEvaluationCode_sum_puncturedLine
            K dimension dimensionPositive message target direction).symm,
            inductionHypothesis directions equalLength⟩

/-- Under the exact direction-counting condition, every request list has a
pairwise-disjoint schedule whose code-symbol sums recover the whole list. -/
theorem exists_disjoint_paperEvaluationCode_recovery
    (K : Type*)
    [Fintype K] [Field K] [DecidableEq K] [CharP K 2]
    (dimension : Nat)
    (dimensionPositive : 0 < dimension)
    (message :
      (Fin dimension ->
        Fin (resourceGridWidth (Fintype.card K) dimension)) -> K)
    (targets : List (Fin dimension -> K))
    (cardBound : targets.length * (Nat.card K - 1) <
      Nat.card (ℙ K (Fin dimension -> K))) :
    ∃ directions : List (ℙ K (Fin dimension -> K)),
      ValidSchedule targets directions ∧
        (recoverySets targets directions).map
            (fun set => ∑ point ∈ set,
              paperEvaluationCode K dimension message point) =
          targets.map (paperEvaluationCode K dimension message) := by
  obtain ⟨directions, schedule⟩ := exists_validSchedule targets cardBound
  refine ⟨directions, schedule, ?_⟩
  exact paperEvaluationCode_recoverySets K dimension dimensionPositive
    message targets directions schedule.1

/-- Paper-facing form under the simpler condition
`requests * |K| < |projective directions|`. -/
theorem exists_disjoint_paperEvaluationCode_recovery_of_mul_card_lt
    (K : Type*)
    [Fintype K] [Field K] [DecidableEq K] [CharP K 2]
    (dimension : Nat)
    (dimensionPositive : 0 < dimension)
    (message :
      (Fin dimension ->
        Fin (resourceGridWidth (Fintype.card K) dimension)) -> K)
    (targets : List (Fin dimension -> K))
    (cardBound : targets.length * Nat.card K <
      Nat.card (ℙ K (Fin dimension -> K))) :
    ∃ directions : List (ℙ K (Fin dimension -> K)),
      ValidSchedule targets directions ∧
        (recoverySets targets directions).map
            (fun set => ∑ point ∈ set,
              paperEvaluationCode K dimension message point) =
          targets.map (paperEvaluationCode K dimension message) := by
  obtain ⟨directions, schedule⟩ :=
    exists_validSchedule_of_mul_card_lt targets cardBound
  refine ⟨directions, schedule, ?_⟩
  exact paperEvaluationCode_recoverySets K dimension dimensionPositive
    message targets directions schedule.1

end MassProduction
end Algebraic
