/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.MassProduction.CodeParameters
public import Complexitylib.Algebraic.MassProduction.ShannonCircuit
public import Mathlib.Data.Fintype.EquivFin

/-!
# Lupanov truth-table blocks

This module defines the padded truth-table blocks and sparse support
expressions used by finite Lupanov synthesis. It contains only the table
representation and its elementary cost and one-hot semantics.
-/

@[expose] public section

namespace Algebraic
namespace MassProduction
namespace LupanovSynthesis

open scoped BigOperators
open ShannonSynthesis

/-- Number of consecutive address-table blocks of length `blockSize`. -/
def blockCount (addressWidth blockSize : Nat) : Nat :=
  (2 ^ addressWidth) ⌈/⌉ blockSize

/-- Number of Boolean patterns on one address block. -/
def patternCount (blockSize : Nat) : Nat :=
  2 ^ blockSize

/-- The block containing a given address assignment. -/
def selectedBlock
    (blockSizePositive : 0 < blockSize)
    (address : Fin (2 ^ addressWidth)) :
    Fin (blockCount addressWidth blockSize) := by
  refine ⟨address.val / blockSize, ?_⟩
  by_contra notBelow
  have countLe : blockCount addressWidth blockSize <=
      address.val / blockSize := Nat.le_of_not_gt notBelow
  have capacity : 2 ^ addressWidth <=
      blockCount addressWidth blockSize * blockSize := by
    unfold blockCount
    simpa only [Nat.mul_comm] using
      (ceilDiv_le_iff_le_mul blockSizePositive).mp
        (show (2 ^ addressWidth) ⌈/⌉ blockSize <=
          (2 ^ addressWidth) ⌈/⌉ blockSize from le_rfl)
  have quotientPart :
      (address.val / blockSize) * blockSize <= address.val :=
    Nat.div_mul_le_self address.val blockSize
  have : 2 ^ addressWidth <= address.val :=
    capacity.trans <| (Nat.mul_le_mul_right blockSize countLe).trans quotientPart
  exact (Nat.not_le_of_lt address.isLt) this

/-- Offset of an address assignment inside its selected block. -/
def selectedOffset
    (blockSizePositive : 0 < blockSize)
    (address : Fin (2 ^ addressWidth)) : Fin blockSize :=
  ⟨address.val % blockSize, Nat.mod_lt _ blockSizePositive⟩

/-- The padded truth-table column on one consecutive address block.  Rows
beyond the address table in the last block are fixed to false. -/
noncomputable def blockColumn
    (function : ScalarFunction Bool (addressWidth + dataWidth))
    (block : Fin (blockCount addressWidth blockSize))
    (data : Fin (2 ^ dataWidth)) : Fin blockSize -> Bool :=
  fun offset =>
    if rowValid : block.val * blockSize + offset.val < 2 ^ addressWidth then
      function (Fin.append
        (assignmentBits addressWidth
          ⟨block.val * blockSize + offset.val, rowValid⟩)
        (assignmentBits dataWidth data))
    else
      false

/-- Canonical index of the padded pattern in one truth-table block. -/
noncomputable def blockPattern
    (function : ScalarFunction Bool (addressWidth + dataWidth))
    (block : Fin (blockCount addressWidth blockSize))
    (data : Fin (2 ^ dataWidth)) : Fin (patternCount blockSize) :=
  bitVectorEquiv blockSize (blockColumn function block data)

@[simp] theorem assignmentBits_blockPattern
    (function : ScalarFunction Bool (addressWidth + dataWidth))
    (block : Fin (blockCount addressWidth blockSize))
    (data : Fin (2 ^ dataWidth))
    (offset : Fin blockSize) :
    assignmentBits blockSize (blockPattern function block data) offset =
      blockColumn function block data offset := by
  unfold blockPattern
  rw [assignmentBits_bitVectorEquiv]

/-- Data assignments whose padded column has one fixed block pattern. -/
noncomputable def rightSupport
    (function : ScalarFunction Bool (addressWidth + dataWidth))
    (block : Fin (blockCount addressWidth blockSize))
    (pattern : Fin (patternCount blockSize)) :
    Finset (Fin (2 ^ dataWidth)) :=
  Finset.univ.filter fun data => blockPattern function block data = pattern

@[simp] theorem mem_rightSupport
    (function : ScalarFunction Bool (addressWidth + dataWidth))
    (block : Fin (blockCount addressWidth blockSize))
    (pattern : Fin (patternCount blockSize))
    (data : Fin (2 ^ dataWidth)) :
    data ∈ rightSupport function block pattern ↔
      blockPattern function block data = pattern := by
  simp [rightSupport]

/-- OR exactly the input wires in a finite support.  Unlike a full-width OR,
its charged size is the cardinality of the support. -/
noncomputable def supportExpression
    (support : Finset (Fin inputs)) : DeMorgan.Expression inputs :=
  DeMorgan.Expression.finOr support.card fun index =>
    .input ((support.equivFin).symm index).1

theorem supportExpression_standardCost
    (support : Finset (Fin inputs)) :
    (supportExpression support).standardCost = support.card := by
  rw [supportExpression, DeMorgan.Expression.finOr_standardCost]
  simp [DeMorgan.Expression.standardCost]

/-- On a one-hot vector, a sparse OR is exactly support membership of the
selected coordinate. -/
theorem supportExpression_eval_oneHot
    (support : Finset (Fin inputs))
    (flags : Fin inputs -> Bool)
    (selected : Fin inputs)
    (selectedTrue : flags selected = true)
    (unique : forall index, flags index = true -> index = selected) :
    (supportExpression support).eval flags =
      decide (selected ∈ support) := by
  apply Bool.eq_iff_iff.mpr
  rw [supportExpression, DeMorgan.Expression.finOr_eval,
    DeMorgan.Expression.finOrValue_eq_true_iff, decide_eq_true_eq]
  constructor
  · rintro ⟨index, indexTrue⟩
    simp only [DeMorgan.Expression.eval] at indexTrue
    have selectedIndex : ((support.equivFin).symm index).1 = selected :=
      unique _ indexTrue
    simp [← selectedIndex]
  · intro selectedMember
    let member : support := ⟨selected, selectedMember⟩
    refine ⟨support.equivFin member, ?_⟩
    simp only [DeMorgan.Expression.eval]
    simpa [member] using selectedTrue

/-- The sparse data-pattern expression for one block and pattern. -/
noncomputable def rightExpression
    (function : ScalarFunction Bool (addressWidth + dataWidth))
    (block : Fin (blockCount addressWidth blockSize))
    (pattern : Fin (patternCount blockSize)) :
    DeMorgan.Expression (2 ^ dataWidth) :=
  supportExpression (rightSupport function block pattern)

theorem rightExpression_standardCost
    (function : ScalarFunction Bool (addressWidth + dataWidth))
    (block : Fin (blockCount addressWidth blockSize))
    (pattern : Fin (patternCount blockSize)) :
    (rightExpression function block pattern).standardCost =
      (rightSupport function block pattern).card := by
  exact supportExpression_standardCost _

/-- The right supports for a fixed block partition all data assignments. -/
theorem sum_rightSupport_card
    (function : ScalarFunction Bool (addressWidth + dataWidth))
    (block : Fin (blockCount addressWidth blockSize)) :
    (∑ pattern : Fin (patternCount blockSize),
        (rightSupport function block pattern).card) = 2 ^ dataWidth := by
  classical
  have partition := Finset.card_eq_sum_card_fiberwise
    (s := (Finset.univ : Finset (Fin (2 ^ dataWidth))))
    (t := (Finset.univ : Finset (Fin (patternCount blockSize))))
    (f := blockPattern function block)
    (by simp)
  simpa [rightSupport] using partition.symm

end LupanovSynthesis
end MassProduction
end Algebraic
