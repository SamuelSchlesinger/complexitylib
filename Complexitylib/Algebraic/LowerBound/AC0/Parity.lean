/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.AC0.DecisionTreeTrace
public import Complexitylib.Algebraic.LowerBound.GateElimination.Xor
public import Complexitylib.Algebraic.CircuitFamily

/-!
# Parity under partial assignments

This module proves the exact decision-tree resilience of parity needed by the
AC0 lower bound. It reuses the library's canonical Boolean-ring parity
function from the gate-elimination development.

For every partial assignment `rho`, the restricted parity function has
deterministic decision-tree depth exactly `rho.liveCount`. The lower bound is
an adversary argument on one evaluation path: flipping any live coordinate
changes parity, so every live coordinate must occur among that path's
queries. The matching upper bound is the structural Shannon tree over the
live coordinates.
-/

@[expose] public section

namespace Algebraic
namespace AC0
namespace Parity

/-- Canonical parity scalar function, reusing the gate-elimination
definition. -/
def function (n : Nat) : ScalarFunction Bool n :=
  GateElimination.Xor.parity

/-- Parity as a one-output circuit target. -/
def target (n : Nat) : Target Bool n 1 :=
  GateElimination.Xor.parityTarget n

@[simp] theorem target_apply
    (input : Fin n -> Bool)
    (output : Fin 1) :
    target n input output = function n input := rfl

/-- The all-input-width family of parity targets. -/
def targetFamily : Target.Family Bool 1 :=
  target

@[simp] theorem targetFamily_apply (n : Nat) :
    targetFamily n = target n := rfl

/-- Flip one coordinate of a Boolean input. -/
def flip
    (input : Fin n -> Bool)
    (selected : Fin n) : Fin n -> Bool :=
  fun index => if index = selected then !(input index) else input index

@[simp] theorem flip_selected
    (input : Fin n -> Bool)
    (selected : Fin n) :
    flip input selected selected = !(input selected) := by
  simp [flip]

theorem flip_other
    (input : Fin n -> Bool)
    (selected index : Fin n)
    (different : index ≠ selected) :
    flip input selected index = input index := by
  simp [flip, different]

/-- Flipping a coordinate left live by `rho` changes restricted parity on
every input. -/
theorem restrict_ne_flip_of_live
    (rho : PartialAssignment n)
    (selected : Fin n)
    (live : selected ∈ rho.liveVariables)
    (input : Fin n -> Bool) :
    (function n).restrict rho (flip input selected) ≠
      (function n).restrict rho input := by
  have selectedLive : rho selected = none :=
    (PartialAssignment.mem_liveVariables rho selected).1 live
  have agree : forall index, index ≠ selected ->
      rho.apply (flip input selected) index = rho.apply input index := by
    intro index different
    cases fixed : rho index with
    | none =>
        simp [PartialAssignment.apply, fixed,
          flip_other input selected index different]
    | some value => simp [PartialAssignment.apply, fixed]
  have different :
      rho.apply (flip input selected) selected ≠
        rho.apply input selected := by
    rw [PartialAssignment.apply_of_live _ _ selectedLive,
      PartialAssignment.apply_of_live _ _ selectedLive,
      flip_selected]
    cases input selected <;> simp
  have changed := GateElimination.Xor.target_ne_of_selected_ne
    ⟨n, false⟩ selected
    (rho.apply (flip input selected)) (rho.apply input)
    agree different
  simpa [function, ScalarFunction.restrict_apply,
    GateElimination.Xor.target] using changed

/-- Every live parity coordinate must occur on every evaluation path of a
tree computing the restricted function. -/
theorem liveVariables_subset_evaluationPath
    (rho : PartialAssignment n)
    (tree : DecisionTree n)
    (computes : tree.Computes ((function n).restrict rho))
    (input : Fin n -> Bool) :
    rho.liveVariables ⊆
      (DecisionTree.PathStep.indices
        (tree.evaluationPath input)).toFinset := by
  intro selected live
  by_contra absent
  have treeEqual := tree.eval_eq_of_agree_on_evaluationPath
    input (flip input selected) (by
      intro index present
      exact flip_other input selected index fun equal => by
        subst index
        exact absent present)
  exact restrict_ne_flip_of_live rho selected live input <| by
    rw [← computes (flip input selected), ← computes input]
    exact treeEqual

/-- Every tree computing parity restricted by `rho` has depth at least the
number of variables still live. -/
theorem depthAtLeast_liveCount
    (rho : PartialAssignment n) :
    DecisionTree.DepthAtLeast ((function n).restrict rho) rho.liveCount := by
  intro tree computes
  let input : Fin n -> Bool := fun _ => false
  have subset := liveVariables_subset_evaluationPath rho tree computes input
  calc
    rho.liveCount = rho.liveVariables.card := rfl
    _ <= (DecisionTree.PathStep.indices
          (tree.evaluationPath input)).toFinset.card :=
      Finset.card_le_card subset
    _ <= (DecisionTree.PathStep.indices
          (tree.evaluationPath input)).length :=
      List.toFinset_card_le _
    _ = (tree.evaluationPath input).length := by
      simp [DecisionTree.PathStep.indices]
    _ <= tree.depth := tree.evaluationPath_length_le_depth input

/-- The structural Shannon tree over the live coordinates gives the matching
upper bound. -/
theorem depthAtMost_liveCount
    (rho : PartialAssignment n) :
    DecisionTree.DepthAtMost ((function n).restrict rho) rho.liveCount := by
  let indices := rho.liveVariables.toList
  let restricted := (function n).restrict rho
  have nodup : indices.Nodup := by
    exact rho.liveVariables.nodup_toList
  have depends : DependsOnlyOn restricted indices.toFinset := by
    simpa [indices, restricted] using
      ScalarFunction.restrict_dependsOnlyOn_live (function n) rho
  refine ⟨DecisionTree.build indices restricted,
    DecisionTree.build_computes_of_dependsOnlyOn
      indices restricted nodup depends, ?_⟩
  calc
    (DecisionTree.build indices restricted).depth <= indices.length :=
      DecisionTree.depth_build_le_length indices restricted
    _ = rho.liveCount := by
      simp [indices, PartialAssignment.liveCount]

/-- Exact semantic characterization of the depth of restricted parity. -/
theorem depthAtMost_iff_liveCount_le
    (rho : PartialAssignment n)
    (bound : Nat) :
    DecisionTree.DepthAtMost ((function n).restrict rho) bound ↔
      rho.liveCount <= bound := by
  constructor
  · rintro ⟨tree, computes, treeBound⟩
    exact (depthAtLeast_liveCount rho tree computes).trans treeBound
  · intro liveBound
    exact (depthAtMost_liveCount rho).mono liveBound

end Parity
end AC0
end Algebraic
