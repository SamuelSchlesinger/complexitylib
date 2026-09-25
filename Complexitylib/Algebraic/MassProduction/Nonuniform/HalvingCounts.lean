/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.MassProduction.Nonuniform.PhaseMenu
public import Complexitylib.Algebraic.MassProduction.SortingNetwork

/-!
# Exact counts for fixed halving phases

A successful menu candidate contains enough clean requests for a fixed
prefix. Power-of-two batches halve until the singleton phase accepts the
last request; no runtime counters are needed for these sizes.
-/

@[expose] public section

namespace Algebraic.MassProduction.Nonuniform

open Sorting
open scoped LinearAlgebra.Projectivization

/-- The half-clean predicate provides the rounded-up acceptance count. -/
theorem HalfClean.cleanCount
    {K V : Type*} [Field K] [Finite K] [AddCommGroup V] [Module K V]
    (state : PhaseState V (ℙ K V) capacity active)
    (candidate : Fin active → ℙ K V) (successful : HalfClean state candidate) :
    (active + 1) / 2 ≤ Nat.card {index : Fin active //
      Clean (fun index direction => puncturedLine (state.2 index) direction)
        (phaseOccupied state) candidate index} := by
  unfold HalfClean at successful
  omega

/-- Number accepted by the phase whose pending batch has `2^depth` requests. -/
def acceptedCount (depth : Nat) : Nat := (networkRecords depth + 1) / 2

/-- Number remaining after the fixed clean prefix is accepted. -/
def pendingCount (depth : Nat) : Nat := networkRecords depth / 2

/-- Every nonempty power-of-two phase accepts at least one request. -/
theorem acceptedCount_positive (depth : Nat) : 0 < acceptedCount depth := by
  have positive : 0 < networkRecords depth := by simp
  unfold acceptedCount
  omega

/-- The accepted prefix fits in the current request array. -/
theorem acceptedCount_le (depth : Nat) : acceptedCount depth ≤ networkRecords depth := by
  have positive : 0 < networkRecords depth := by simp
  unfold acceptedCount
  omega

/-- Accepted and pending counts partition the batch exactly. -/
theorem acceptedCount_add_pendingCount (depth : Nat) :
    acceptedCount depth + pendingCount depth = networkRecords depth := by
  unfold acceptedCount pendingCount
  omega

/-- The singleton phase accepts its only request. -/
@[simp] theorem acceptedCount_zero : acceptedCount 0 = 1 := rfl

/-- The singleton phase leaves no pending requests. -/
@[simp] theorem pendingCount_zero : pendingCount 0 = 0 := rfl

/-- A larger phase accepts exactly the next smaller power of two. -/
@[simp] theorem acceptedCount_succ (depth : Nat) : acceptedCount (depth + 1) = networkRecords depth := by
  simp only [acceptedCount, networkRecords]
  omega

/-- A larger phase leaves exactly the next smaller power of two. -/
@[simp] theorem pendingCount_succ (depth : Nat) : pendingCount (depth + 1) = networkRecords depth := by
  simp only [pendingCount, networkRecords]
  omega

end Algebraic.MassProduction.Nonuniform
