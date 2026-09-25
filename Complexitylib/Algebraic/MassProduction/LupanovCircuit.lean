/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.MassProduction.LupanovPatternBank

/-!
# Finite Lupanov circuit

This module recombines the two pattern banks into the finite Lupanov
block-table circuit. It gives an explicit cost ledger and proves exact
evaluation and `ComputesWith` theorems for every positive block size.
-/

@[expose] public section

namespace Algebraic
namespace MassProduction
namespace LupanovSynthesis

open ShannonSynthesis

/-! ## Recombination and the complete finite circuit -/

/-- Number of flattened `(block, pattern)` flags in either bank. -/
@[reducible] def bankWidth (addressWidth blockSize : Nat) : Nat :=
  blockCount addressWidth blockSize * patternCount blockSize

/-- Program-gate count of both flattened pattern banks. -/
@[reducible] noncomputable def patternBankGateCount
    (function : ScalarFunction Bool (addressWidth + dataWidth))
    (blockSize : Nat) : Nat :=
  leftBankGateCount addressWidth blockSize +
    rightBankGateCount function blockSize

/-- Compute the left and right pattern banks side by side. -/
noncomputable def patternBankCircuit
    (function : ScalarFunction Bool (addressWidth + dataWidth))
    (blockSize : Nat) :
    Circuit DeMorgan.signature (2 ^ addressWidth + 2 ^ dataWidth)
      (patternBankGateCount function blockSize)
      (bankWidth addressWidth blockSize + bankWidth addressWidth blockSize) :=
  (leftBankCircuit addressWidth dataWidth blockSize).parallel
    (rightBankCircuit function blockSize)

/-- Coordinate of a left-bank flag in the combined pattern state. -/
def leftPatternInput
    (index : Fin (bankWidth addressWidth blockSize)) :
    Fin (bankWidth addressWidth blockSize + bankWidth addressWidth blockSize) :=
  Fin.castAdd _ index

/-- Coordinate of the corresponding right-bank flag. -/
def rightPatternInput
    (index : Fin (bankWidth addressWidth blockSize)) :
    Fin (bankWidth addressWidth blockSize + bankWidth addressWidth blockSize) :=
  Fin.natAdd _ index

@[simp] theorem patternBankCircuit_eval_left
    (function : ScalarFunction Bool (addressWidth + dataWidth))
    (blockSize : Nat)
    (state : Fin (2 ^ addressWidth + 2 ^ dataWidth) -> Bool)
    (block : Fin (blockCount addressWidth blockSize))
    (pattern : Fin (patternCount blockSize)) :
    (patternBankCircuit function blockSize).eval DeMorgan.interpretation state
        (leftPatternInput (finProdFinEquiv (block, pattern))) =
      (leftExpression addressWidth blockSize block pattern).eval
        (fun address => state (Fin.castAdd (2 ^ dataWidth) address)) := by
  rw [patternBankCircuit, Circuit.eval_parallel]
  unfold leftPatternInput
  rw [Fin.append_left, leftBankCircuit_eval]

@[simp] theorem patternBankCircuit_eval_right
    (function : ScalarFunction Bool (addressWidth + dataWidth))
    (blockSize : Nat)
    (state : Fin (2 ^ addressWidth + 2 ^ dataWidth) -> Bool)
    (block : Fin (blockCount addressWidth blockSize))
    (pattern : Fin (patternCount blockSize)) :
    (patternBankCircuit function blockSize).eval DeMorgan.interpretation state
        (rightPatternInput (finProdFinEquiv (block, pattern))) =
      (rightExpression function block pattern).eval
        (fun data => state (Fin.natAdd (2 ^ addressWidth) data)) := by
  rw [patternBankCircuit, Circuit.eval_parallel]
  unfold rightPatternInput
  rw [Fin.append_right, rightBankCircuit_eval]

theorem patternBankCircuit_cost
    (function : ScalarFunction Bool (addressWidth + dataWidth))
    (blockSize : Nat) :
    (patternBankCircuit function blockSize).cost DeMorgan.standardCost =
      blockCount addressWidth blockSize *
          (patternCount blockSize * blockSize) +
        blockCount addressWidth blockSize * 2 ^ dataWidth := by
  rw [patternBankCircuit, Circuit.cost_parallel,
    leftBankCircuit_cost, rightBankCircuit_cost]

/-- Conjoin corresponding flags in the two pattern banks. -/
def matchingPatternTerm
    (addressWidth blockSize : Nat)
    (index : Fin (bankWidth addressWidth blockSize)) :
    DeMorgan.Expression
      (bankWidth addressWidth blockSize + bankWidth addressWidth blockSize) :=
  .and (.input (leftPatternInput index)) (.input (rightPatternInput index))

/-- OR all matching block-pattern conjunctions. -/
def synthesisExpression
    (addressWidth blockSize : Nat) :
    DeMorgan.Expression
      (bankWidth addressWidth blockSize + bankWidth addressWidth blockSize) :=
  DeMorgan.Expression.finOr (bankWidth addressWidth blockSize)
    (matchingPatternTerm addressWidth blockSize)

theorem synthesisExpression_standardCost
    (addressWidth blockSize : Nat) :
    (synthesisExpression addressWidth blockSize).standardCost =
      2 * bankWidth addressWidth blockSize := by
  rw [synthesisExpression, DeMorgan.Expression.finOr_standardCost]
  simp [matchingPatternTerm, DeMorgan.Expression.standardCost]
  omega

/-- Program-gate count of all three stages of finite Lupanov synthesis. -/
@[reducible] noncomputable def synthesisGateCount
    (function : ScalarFunction Bool (addressWidth + dataWidth))
    (blockSize : Nat) : Nat :=
  splitMintermGateCount addressWidth dataWidth +
    patternBankGateCount function blockSize +
      (synthesisExpression addressWidth blockSize).gateCount

/-- The finite Lupanov block-table circuit. -/
noncomputable def circuit
    (function : ScalarFunction Bool (addressWidth + dataWidth))
    (blockSize : Nat) :
    Circuit DeMorgan.signature (addressWidth + dataWidth)
      (synthesisGateCount function blockSize) 1 :=
  (synthesisExpression addressWidth blockSize).circuit.comp
    ((patternBankCircuit function blockSize).comp
      (splitMintermCircuit addressWidth dataWidth))

/-- Explicit finite cost ledger. -/
def costBound
    (addressWidth dataWidth blockSize : Nat) : Nat :=
  4 * 2 ^ addressWidth + 4 * 2 ^ dataWidth +
    blockCount addressWidth blockSize *
        (patternCount blockSize * blockSize) +
      blockCount addressWidth blockSize * 2 ^ dataWidth +
        2 * bankWidth addressWidth blockSize

theorem circuit_cost_le
    (function : ScalarFunction Bool (addressWidth + dataWidth))
    (blockSize : Nat) :
    (circuit function blockSize).cost DeMorgan.standardCost <=
      costBound addressWidth dataWidth blockSize := by
  rw [circuit, Circuit.cost_comp, Circuit.cost_comp,
    DeMorgan.Expression.circuit_cost, synthesisExpression_standardCost,
    patternBankCircuit_cost, splitMintermCircuit,
    Circuit.cost_parallel, Circuit.cost_mapInputs, Circuit.cost_mapInputs]
  have addressBound := mintermCircuit_cost_le addressWidth
  have dataBound := mintermCircuit_cost_le dataWidth
  unfold costBound
  omega

/-! ## Exact semantics -/

/-- The address-side block expression, fed by the shared minterm table, is
true exactly when one of its literal rows is the selected address and the
corresponding pattern bit is true. -/
theorem leftExpression_eval_minterms_true_iff
    (addressWidth blockSize : Nat)
    (block : Fin (blockCount addressWidth blockSize))
    (pattern : Fin (patternCount blockSize))
    (addressInput : Fin addressWidth -> Bool) :
    (leftExpression addressWidth blockSize block pattern).eval
          ((mintermCircuit addressWidth).eval
            DeMorgan.interpretation addressInput) = true ↔
      exists offset : Fin blockSize,
        exists rowValid : block.val * blockSize + offset.val <
            2 ^ addressWidth,
          (⟨block.val * blockSize + offset.val, rowValid⟩ :
              Fin (2 ^ addressWidth)) =
              bitVectorEquiv addressWidth addressInput /\
            assignmentBits blockSize pattern offset = true := by
  rw [leftExpression, DeMorgan.Expression.finOr_eval,
    DeMorgan.Expression.finOrValue_eq_true_iff]
  constructor
  · rintro ⟨offset, offsetTrue⟩
    rw [leftTerm_eval] at offsetTrue
    split at offsetTrue
    · rename_i rowValid
      rw [Bool.and_eq_true] at offsetTrue
      refine ⟨offset, rowValid, ?_, offsetTrue.2⟩
      rw [mintermCircuit_eval] at offsetTrue
      exact (of_decide_eq_true offsetTrue.1).symm
    · contradiction
  · rintro ⟨offset, rowValid, rowSelected, patternTrue⟩
    refine ⟨offset, ?_⟩
    rw [leftTerm_eval]
    simp only [dite_eq_left rowValid, Bool.and_eq_true]
    constructor
    · rw [mintermCircuit_eval]
      exact decide_eq_true rowSelected.symm
    · exact patternTrue

/-- The data-side sparse expression, fed by the shared minterm table, is the
indicator of the selected data column having the requested block pattern. -/
theorem rightExpression_eval_minterms
    (function : ScalarFunction Bool (addressWidth + dataWidth))
    (blockSize : Nat)
    (block : Fin (blockCount addressWidth blockSize))
    (pattern : Fin (patternCount blockSize))
    (dataInput : Fin dataWidth -> Bool) :
    (rightExpression function block pattern).eval
          ((mintermCircuit dataWidth).eval
            DeMorgan.interpretation dataInput) =
      decide (blockPattern function block
        (bitVectorEquiv dataWidth dataInput) = pattern) := by
  unfold rightExpression
  let selected := bitVectorEquiv dataWidth dataInput
  have sparse := supportExpression_eval_oneHot
    (rightSupport function block pattern)
    ((mintermCircuit dataWidth).eval DeMorgan.interpretation dataInput)
    selected
    (by
      rw [mintermCircuit_eval]
      simp [selected])
    (by
      intro assignment assignmentTrue
      rw [mintermCircuit_eval] at assignmentTrue
      simpa [selected] using (of_decide_eq_true assignmentTrue).symm)
  simpa [rightSupport, selected] using sparse

/-- The finite block-table circuit computes the supplied Boolean function
exactly. -/
theorem circuit_eval
    (blockSizePositive : 0 < blockSize)
    (function : ScalarFunction Bool (addressWidth + dataWidth))
    (input : Fin (addressWidth + dataWidth) -> Bool) :
    (circuit function blockSize).eval DeMorgan.interpretation input 0 =
      function input := by
  rw [circuit, Circuit.eval_comp, Circuit.eval_comp,
    DeMorgan.Expression.circuit_eval]
  apply Bool.eq_iff_iff.mpr
  rw [synthesisExpression, DeMorgan.Expression.finOr_eval,
    DeMorgan.Expression.finOrValue_eq_true_iff]
  constructor
  · rintro ⟨flat, flatTrue⟩
    let pair := (finProdFinEquiv :
      Fin (blockCount addressWidth blockSize) ×
        Fin (patternCount blockSize) ≃
          Fin (bankWidth addressWidth blockSize)).symm flat
    let block := pair.1
    let pattern := pair.2
    have flatEquality : finProdFinEquiv (block, pattern) = flat := by
      exact (finProdFinEquiv :
        Fin (blockCount addressWidth blockSize) ×
          Fin (patternCount blockSize) ≃
            Fin (bankWidth addressWidth blockSize)).apply_symm_apply flat
    rw [matchingPatternTerm, DeMorgan.Expression.eval,
      Bool.and_eq_true, ← flatEquality] at flatTrue
    simp only [DeMorgan.Expression.eval] at flatTrue
    have leftTrue := flatTrue.1
    have rightTrue := flatTrue.2
    rw [patternBankCircuit_eval_left, splitMintermCircuit_eval] at leftTrue
    simp only [Fin.append_left] at leftTrue
    rw [patternBankCircuit_eval_right, splitMintermCircuit_eval] at rightTrue
    simp only [Fin.append_right] at rightTrue
    obtain ⟨offset, rowValid, rowSelected, patternTrue⟩ :=
      (leftExpression_eval_minterms_true_iff
        addressWidth blockSize block pattern
          (addressInput dataWidth input)).mp leftTrue
    rw [rightExpression_eval_minterms] at rightTrue
    have selectedPattern :
        blockPattern function block
            (bitVectorEquiv dataWidth (dataInput addressWidth input)) =
          pattern :=
      of_decide_eq_true rightTrue
    rw [← selectedPattern, assignmentBits_blockPattern] at patternTrue
    unfold blockColumn at patternTrue
    simp only [dite_eq_left rowValid] at patternTrue
    rw [rowSelected, assignmentBits_bitVectorEquiv,
      assignmentBits_bitVectorEquiv] at patternTrue
    rw [append_addressInput_dataInput] at patternTrue
    exact patternTrue
  · intro functionTrue
    let address := bitVectorEquiv addressWidth (addressInput dataWidth input)
    let data := bitVectorEquiv dataWidth (dataInput addressWidth input)
    let block := selectedBlock (addressWidth := addressWidth)
      blockSizePositive address
    let offset := selectedOffset blockSizePositive address
    let pattern := blockPattern function block data
    let flat : Fin (bankWidth addressWidth blockSize) :=
      finProdFinEquiv (block, pattern)
    have rowEquality :
        block.val * blockSize + offset.val = address.val := by
      simpa [block, offset, selectedBlock, selectedOffset] using
        Nat.div_add_mod' address.val blockSize
    have rowValid :
        block.val * blockSize + offset.val < 2 ^ addressWidth := by
      simpa only [rowEquality] using address.isLt
    have rowSelected :
        (⟨block.val * blockSize + offset.val, rowValid⟩ :
            Fin (2 ^ addressWidth)) = address := by
      apply Fin.ext
      exact rowEquality
    have patternTrue :
        assignmentBits blockSize pattern offset = true := by
      rw [show pattern = blockPattern function block data by rfl,
        assignmentBits_blockPattern]
      unfold blockColumn
      simp only [dite_eq_left rowValid]
      rw [rowSelected]
      have addressDecoded : assignmentBits addressWidth address =
          addressInput dataWidth input := by
        exact assignmentBits_bitVectorEquiv _
      have dataDecoded : assignmentBits dataWidth data =
          dataInput addressWidth input := by
        exact assignmentBits_bitVectorEquiv _
      rw [addressDecoded, dataDecoded, append_addressInput_dataInput]
      exact functionTrue
    refine ⟨flat, ?_⟩
    rw [matchingPatternTerm, DeMorgan.Expression.eval, Bool.and_eq_true]
    constructor
    · dsimp only [flat]
      simp only [DeMorgan.Expression.eval]
      rw [patternBankCircuit_eval_left, splitMintermCircuit_eval]
      simp only [Fin.append_left]
      apply (leftExpression_eval_minterms_true_iff
        addressWidth blockSize block pattern
          (addressInput dataWidth input)).mpr
      exact ⟨offset, rowValid, rowSelected, patternTrue⟩
    · dsimp only [flat]
      simp only [DeMorgan.Expression.eval]
      rw [patternBankCircuit_eval_right, splitMintermCircuit_eval]
      simp only [Fin.append_right]
      rw [rightExpression_eval_minterms]
      exact decide_eq_true rfl

theorem circuit_computes
    (blockSizePositive : 0 < blockSize)
    (function : ScalarFunction Bool (addressWidth + dataWidth)) :
    (circuit function blockSize).ComputesWith DeMorgan.interpretation
      (scalarTarget function) := by
  intro input
  funext output
  have outputZero : output = 0 := Fin.eq_zero output
  subst output
  exact circuit_eval blockSizePositive function input

end LupanovSynthesis
end MassProduction
end Algebraic
