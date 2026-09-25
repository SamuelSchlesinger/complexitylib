/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.MassProduction.Nonuniform.BufferIterationCost

/-!
# Initial and completed scheduler states

The initial buffer has no occupied lines and keeps requests in their
original order. A completed buffer determines a permutation of all request
identities and, after undoing that permutation, a disjoint recovery line
for every original target.
-/

@[expose] public section

namespace Algebraic.MassProduction.Nonuniform.BufferModel

open scoped LinearAlgebra.Projectivization

/-- Empty occupied state, with every request pending in its original order. -/
def State.initial (total dimension width : Nat) : State total 0 total dimension width where
  order := Equiv.emptySum (Fin 0) (Fin total)
  directions := Fin.elim0

/-- Initial pending positions are original request identities. -/
theorem State.initial_order (request : Fin total) :
    (State.initial total dimension width).order (.inr request) = request := rfl

/-- The empty occupied state satisfies the disjointness invariant. -/
theorem State.initial_wellScheduled (targets : Fin total → Fin dimension → BinaryExtension width) :
    WellScheduled (State.initial total dimension width) targets := by
  intro left
  exact Fin.elim0 left

/-- The initial encoded input is just the original pending records, with
an empty completed prefix. It contains no chosen directions. -/
theorem initial_input (positive : 0 < width)
    (data : Fin total → Fin requestWidth → Bool)
    (targets : Fin total → Fin dimension → BinaryExtension width) :
    input positive (State.initial total dimension width) data targets =
      BufferInput.encode (slots := 2 ^ width) (keyWidth := dimension * width)
        (fun request : Fin 0 => Fin.elim0 request) data := by
  unfold input
  congr 1
  funext request
  exact Fin.elim0 request

/-- Once all requests are completed, the stored order is a permutation. -/
def State.finishedOrder (state : State total total 0 dimension width) : Equiv.Perm (Fin total) :=
  (Equiv.sumEmpty (Fin total) (Fin 0)).symm.trans state.order

/-- Completed positions map to their original request identities. -/
theorem State.finishedOrder_apply (state : State total total 0 dimension width) (request : Fin total) :
    state.finishedOrder request = state.order (.inl request) := rfl

/-- Read the selected direction by original request identity. -/
def State.scheduledDirections (state : State total total 0 dimension width) (request : Fin total) :=
  state.directions (state.finishedOrder.symm request)

/-- Completed-buffer disjointness gives disjoint recovery lines in the
original request order, including when several targets are equal. -/
theorem State.scheduledDirections_disjoint (state : State total total 0 dimension width)
    (targets : Fin total → Fin dimension → BinaryExtension width) (valid : WellScheduled state targets) :
    Pairwise (fun left right =>
      Disjoint (puncturedLine (targets left) (state.scheduledDirections left))
        (puncturedLine (targets right) (state.scheduledDirections right))) := by
  intro left right different
  have distinct : state.finishedOrder.symm left ≠ state.finishedOrder.symm right :=
    fun equal => different (state.finishedOrder.symm.injective equal)
  have disjoint := valid distinct
  simpa only [line, ← State.finishedOrder_apply, Equiv.apply_symm_apply, State.scheduledDirections] using disjoint

end Algebraic.MassProduction.Nonuniform.BufferModel
