/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.MassProduction.Nonuniform.BufferEndpoints
public import Complexitylib.Algebraic.MassProduction.Nonuniform.PaddedLineRecovery

/-!
# Distinct active incidences in a completed buffer

The completed-buffer invariant gives the exact injectivity premise needed
by shared resource scatter. This includes repeated original targets and
the fixed invalid zero slot of every line.
-/

@[expose] public section

namespace Algebraic.MassProduction.Nonuniform.BufferModel

/-- The field point at one flattened completed request/scalar position. -/
noncomputable def incidencePoint (positive : 0 < width)
    (state : State total completed pending dimension width)
    (targets : Fin total → Fin dimension → BinaryExtension width)
    (incidence : Fin (completed * 2 ^ width)) : Fin dimension → BinaryExtension width :=
  let pair := (finProdFinEquiv (m := completed) (n := 2 ^ width)).symm incidence
  PaddedLinePoints.point positive (targets (state.order (.inl pair.1))) (state.directions pair.1) pair.2

/-- Fixed validity of one flattened scalar slot. -/
noncomputable def incidenceValid (positive : 0 < width) (incidence : Fin (completed * 2 ^ width)) : Bool :=
  PaddedLinePoints.valid positive ((finProdFinEquiv (m := completed) (n := 2 ^ width)).symm incidence).2

/-- Disjoint completed lines make all active incidence points distinct. -/
theorem incidencePoint_injective (positive : 0 < width)
    (state : State total completed pending dimension width)
    (targets : Fin total → Fin dimension → BinaryExtension width) (scheduled : WellScheduled state targets)
    (left right : Fin (completed * 2 ^ width))
    (leftActive : incidenceValid positive left = true) (rightActive : incidenceValid positive right = true)
    (samePoint : incidencePoint positive state targets left = incidencePoint positive state targets right) : left = right := by
  obtain ⟨⟨leftRequest, leftSlot⟩, rfl⟩ := finProdFinEquiv.surjective left
  obtain ⟨⟨rightRequest, rightSlot⟩, rfl⟩ := finProdFinEquiv.surjective right
  simp only [incidencePoint, incidenceValid, Equiv.symm_apply_apply] at leftActive rightActive samePoint
  have sameRequest : leftRequest = rightRequest := by
    by_contra different
    have leftMember := PaddedLinePoints.point_mem_puncturedLine positive
      (targets (state.order (.inl leftRequest))) (state.directions leftRequest) leftSlot leftActive
    have rightMember := PaddedLinePoints.point_mem_puncturedLine positive
      (targets (state.order (.inl rightRequest))) (state.directions rightRequest) rightSlot rightActive
    exact Finset.disjoint_left.mp (scheduled different) leftMember (samePoint ▸ rightMember)
  subst rightRequest
  have sameSlot := PaddedLinePoints.point_injective positive _ _ samePoint
  exact congrArg (fun slot => finProdFinEquiv (leftRequest, slot)) sameSlot

end Algebraic.MassProduction.Nonuniform.BufferModel
