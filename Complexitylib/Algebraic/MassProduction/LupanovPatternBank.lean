/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.MassProduction.LupanovTable

/-!
# Lupanov pattern banks

This module constructs the address-side and data-side pattern-recognition
banks used by finite Lupanov synthesis. It proves their exact output
semantics and cost ledgers before any final recombination is performed.
-/

@[expose] public section

namespace Algebraic
namespace MassProduction
namespace LupanovSynthesis

open scoped BigOperators
open ShannonSynthesis

/-! ## The two pattern banks -/

/-- One possible row of a block pattern, gated by its address minterm. -/
noncomputable def leftTerm
    (addressWidth blockSize : Nat)
    (block : Fin (blockCount addressWidth blockSize))
    (pattern : Fin (patternCount blockSize))
    (offset : Fin blockSize) :
    DeMorgan.Expression (2 ^ addressWidth) :=
  if rowValid : block.val * blockSize + offset.val < 2 ^ addressWidth then
    if assignmentBits blockSize pattern offset then
      .input ⟨block.val * blockSize + offset.val, rowValid⟩
    else
      .constant false
  else
    .constant false

@[simp] theorem leftTerm_standardCost
    (addressWidth blockSize : Nat)
    (block : Fin (blockCount addressWidth blockSize))
    (pattern : Fin (patternCount blockSize))
    (offset : Fin blockSize) :
    (leftTerm addressWidth blockSize block pattern offset).standardCost = 0 := by
  unfold leftTerm
  split
  · split <;> rfl
  · rfl

@[simp] theorem leftTerm_eval
    (addressWidth blockSize : Nat)
    (block : Fin (blockCount addressWidth blockSize))
    (pattern : Fin (patternCount blockSize))
    (offset : Fin blockSize)
    (flags : Fin (2 ^ addressWidth) -> Bool) :
    (leftTerm addressWidth blockSize block pattern offset).eval flags =
      if rowValid : block.val * blockSize + offset.val < 2 ^ addressWidth then
        flags ⟨block.val * blockSize + offset.val, rowValid⟩ &&
          assignmentBits blockSize pattern offset
      else
        false := by
  unfold leftTerm
  split <;> rename_i rowValid
  · cases patternBit : assignmentBits blockSize pattern offset <;>
      simp [DeMorgan.Expression.eval]
  · simp [DeMorgan.Expression.eval]

/-- Address-side recognizer of one pattern in one block. -/
noncomputable def leftExpression
    (addressWidth blockSize : Nat)
    (block : Fin (blockCount addressWidth blockSize))
    (pattern : Fin (patternCount blockSize)) :
    DeMorgan.Expression (2 ^ addressWidth) :=
  DeMorgan.Expression.finOr blockSize fun offset =>
    leftTerm addressWidth blockSize block pattern offset

theorem leftExpression_standardCost
    (addressWidth blockSize : Nat)
    (block : Fin (blockCount addressWidth blockSize))
    (pattern : Fin (patternCount blockSize)) :
    (leftExpression addressWidth blockSize block pattern).standardCost =
      blockSize := by
  rw [leftExpression, DeMorgan.Expression.finOr_standardCost]
  simp

/-- Program-gate count of all left recognizers for one block. -/
@[reducible] noncomputable def leftBlockGateCount
    (addressWidth blockSize : Nat)
    (block : Fin (blockCount addressWidth blockSize)) : Nat :=
  ∑ pattern : Fin (patternCount blockSize),
    (leftExpression addressWidth blockSize block pattern).gateCount

/-- All address-side pattern recognizers for one block. -/
noncomputable def leftBlockCircuit
    (addressWidth blockSize : Nat)
    (block : Fin (blockCount addressWidth blockSize)) :
    Circuit DeMorgan.signature (2 ^ addressWidth)
      (leftBlockGateCount addressWidth blockSize block)
      (patternCount blockSize) :=
  Circuit.parallelFin (patternCount blockSize)
    (fun pattern =>
      (leftExpression addressWidth blockSize block pattern).gateCount)
    (fun pattern =>
      (leftExpression addressWidth blockSize block pattern).circuit)

@[simp] theorem leftBlockCircuit_eval
    (addressWidth blockSize : Nat)
    (block : Fin (blockCount addressWidth blockSize))
    (flags : Fin (2 ^ addressWidth) -> Bool)
    (pattern : Fin (patternCount blockSize)) :
    (leftBlockCircuit addressWidth blockSize block).eval
        DeMorgan.interpretation flags pattern =
      (leftExpression addressWidth blockSize block pattern).eval flags := by
  unfold leftBlockCircuit leftBlockGateCount
  rw [Circuit.eval_parallelFin, DeMorgan.Expression.circuit_eval]

theorem leftBlockCircuit_cost
    (addressWidth blockSize : Nat)
    (block : Fin (blockCount addressWidth blockSize)) :
    (leftBlockCircuit addressWidth blockSize block).cost
        DeMorgan.standardCost =
      patternCount blockSize * blockSize := by
  unfold leftBlockCircuit leftBlockGateCount
  rw [Circuit.cost_parallelFin]
  calc
    (∑ pattern : Fin (patternCount blockSize),
        (leftExpression addressWidth blockSize block pattern).circuit.cost
          DeMorgan.standardCost) =
        ∑ _pattern : Fin (patternCount blockSize), blockSize := by
          apply Finset.sum_congr rfl
          intro pattern _membership
          rw [DeMorgan.Expression.circuit_cost,
            leftExpression_standardCost]
    _ = patternCount blockSize * blockSize := by simp

/-- Program-gate count of all sparse right recognizers for one block. -/
@[reducible] noncomputable def rightBlockGateCount
    (function : ScalarFunction Bool (addressWidth + dataWidth))
    (blockSize : Nat)
    (block : Fin (blockCount addressWidth blockSize)) : Nat :=
  ∑ pattern : Fin (patternCount blockSize),
    (rightExpression function block pattern).gateCount

/-- All sparse data-side pattern recognizers for one block. -/
noncomputable def rightBlockCircuit
    (function : ScalarFunction Bool (addressWidth + dataWidth))
    (blockSize : Nat)
    (block : Fin (blockCount addressWidth blockSize)) :
    Circuit DeMorgan.signature (2 ^ dataWidth)
      (rightBlockGateCount function blockSize block)
      (patternCount blockSize) :=
  Circuit.parallelFin (patternCount blockSize)
    (fun pattern => (rightExpression function block pattern).gateCount)
    (fun pattern => (rightExpression function block pattern).circuit)

@[simp] theorem rightBlockCircuit_eval
    (function : ScalarFunction Bool (addressWidth + dataWidth))
    (blockSize : Nat)
    (block : Fin (blockCount addressWidth blockSize))
    (flags : Fin (2 ^ dataWidth) -> Bool)
    (pattern : Fin (patternCount blockSize)) :
    (rightBlockCircuit function blockSize block).eval
        DeMorgan.interpretation flags pattern =
      (rightExpression function block pattern).eval flags := by
  unfold rightBlockCircuit rightBlockGateCount
  rw [Circuit.eval_parallelFin, DeMorgan.Expression.circuit_eval]

theorem rightBlockCircuit_cost
    (function : ScalarFunction Bool (addressWidth + dataWidth))
    (blockSize : Nat)
    (block : Fin (blockCount addressWidth blockSize)) :
    (rightBlockCircuit function blockSize block).cost
        DeMorgan.standardCost = 2 ^ dataWidth := by
  unfold rightBlockCircuit rightBlockGateCount
  rw [Circuit.cost_parallelFin]
  calc
    (∑ pattern : Fin (patternCount blockSize),
        (rightExpression function block pattern).circuit.cost
          DeMorgan.standardCost) =
        ∑ pattern : Fin (patternCount blockSize),
          (rightSupport function block pattern).card := by
            apply Finset.sum_congr rfl
            intro pattern _membership
            rw [DeMorgan.Expression.circuit_cost,
              rightExpression_standardCost]
    _ = 2 ^ dataWidth := sum_rightSupport_card function block

/-- Program-gate count of the complete address-side pattern bank. -/
@[reducible] noncomputable def leftBankGateCount
    (addressWidth blockSize : Nat) : Nat :=
  ∑ block : Fin (blockCount addressWidth blockSize),
    leftBlockGateCount addressWidth blockSize block

/-- The address-side pattern banks, flattened in `(block, pattern)` order. -/
noncomputable def leftBankCircuit
    (addressWidth dataWidth blockSize : Nat) :
    Circuit DeMorgan.signature (2 ^ addressWidth + 2 ^ dataWidth)
      (leftBankGateCount addressWidth blockSize)
      (blockCount addressWidth blockSize * patternCount blockSize) :=
  Circuit.parallelFinVector
    (blockCount addressWidth blockSize) (patternCount blockSize)
    (fun block => leftBlockGateCount addressWidth blockSize block)
    (fun block =>
      (leftBlockCircuit addressWidth blockSize block).mapInputs
        (Fin.castAdd (2 ^ dataWidth)))

@[simp] theorem leftBankCircuit_eval
    (addressWidth dataWidth blockSize : Nat)
    (state : Fin (2 ^ addressWidth + 2 ^ dataWidth) -> Bool)
    (block : Fin (blockCount addressWidth blockSize))
    (pattern : Fin (patternCount blockSize)) :
    (leftBankCircuit addressWidth dataWidth blockSize).eval
        DeMorgan.interpretation state (finProdFinEquiv (block, pattern)) =
      (leftExpression addressWidth blockSize block pattern).eval
        (fun address => state (Fin.castAdd (2 ^ dataWidth) address)) := by
  rw [leftBankCircuit, Circuit.eval_parallelFinVector,
    Circuit.eval_mapInputs, leftBlockCircuit_eval]
  rfl

theorem leftBankCircuit_cost
    (addressWidth dataWidth blockSize : Nat) :
    (leftBankCircuit addressWidth dataWidth blockSize).cost
        DeMorgan.standardCost =
      blockCount addressWidth blockSize *
        (patternCount blockSize * blockSize) := by
  unfold leftBankCircuit leftBankGateCount
  rw [Circuit.cost_parallelFinVector]
  simp only [Circuit.cost_mapInputs, leftBlockCircuit_cost]
  simp

/-- Program-gate count of the complete data-side pattern bank. -/
@[reducible] noncomputable def rightBankGateCount
    (function : ScalarFunction Bool (addressWidth + dataWidth))
    (blockSize : Nat) : Nat :=
  ∑ block : Fin (blockCount addressWidth blockSize),
    rightBlockGateCount function blockSize block

/-- The data-side sparse pattern banks, flattened in `(block, pattern)`
order. -/
noncomputable def rightBankCircuit
    (function : ScalarFunction Bool (addressWidth + dataWidth))
    (blockSize : Nat) :
    Circuit DeMorgan.signature (2 ^ addressWidth + 2 ^ dataWidth)
      (rightBankGateCount function blockSize)
      (blockCount addressWidth blockSize * patternCount blockSize) :=
  Circuit.parallelFinVector
    (blockCount addressWidth blockSize) (patternCount blockSize)
    (fun block => rightBlockGateCount function blockSize block)
    (fun block =>
      (rightBlockCircuit function blockSize block).mapInputs
        (Fin.natAdd (2 ^ addressWidth)))

@[simp] theorem rightBankCircuit_eval
    (function : ScalarFunction Bool (addressWidth + dataWidth))
    (blockSize : Nat)
    (state : Fin (2 ^ addressWidth + 2 ^ dataWidth) -> Bool)
    (block : Fin (blockCount addressWidth blockSize))
    (pattern : Fin (patternCount blockSize)) :
    (rightBankCircuit function blockSize).eval
        DeMorgan.interpretation state (finProdFinEquiv (block, pattern)) =
      (rightExpression function block pattern).eval
        (fun data => state (Fin.natAdd (2 ^ addressWidth) data)) := by
  rw [rightBankCircuit, Circuit.eval_parallelFinVector,
    Circuit.eval_mapInputs, rightBlockCircuit_eval]
  rfl

theorem rightBankCircuit_cost
    (function : ScalarFunction Bool (addressWidth + dataWidth))
    (blockSize : Nat) :
    (rightBankCircuit function blockSize).cost DeMorgan.standardCost =
      blockCount addressWidth blockSize * 2 ^ dataWidth := by
  unfold rightBankCircuit rightBankGateCount
  rw [Circuit.cost_parallelFinVector]
  simp only [Circuit.cost_mapInputs, rightBlockCircuit_cost]
  simp

end LupanovSynthesis
end MassProduction
end Algebraic
