/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.MassProduction.FixedDivision

/-!
# Repeated fixed-base conversion

Repeatedly divide a fixed-width binary input by a positive base.  The circuit
keeps the current fixed-width quotient and appends every remainder in
least-significant-first order, with each remainder represented one-hot.  This
is the runtime base conversion needed by canonical prefix packing.
-/

@[expose] public section

namespace Algebraic
namespace MassProduction
namespace BaseConversion

open FixedDivision

/-- Gate-count recurrence for repeated fixed-base division. -/
@[reducible] noncomputable def gateCount
    (inputWidth : Nat)
    (basePositive : 0 < base) : Nat -> Nat
  | 0 => 0
  | digits + 1 =>
      gateCount inputWidth basePositive digits +
        FixedDivision.prefixGateCount inputWidth basePositive inputWidth

/-- Read the current quotient prefix as the input to one more division. -/
def quotientInputIndex
    (inputWidth retainedBits : Nat) :
    Fin inputWidth -> Fin (inputWidth + retainedBits) :=
  Fin.castAdd retainedBits

/-- Retain an already emitted remainder bit after the quotient prefix. -/
def retainedInputIndex
    (inputWidth retainedBits : Nat) :
    Fin retainedBits -> Fin (inputWidth + retainedBits) :=
  Fin.natAdd inputWidth

/-- Reorder the intermediate `(new quotient, new remainder, old remainders)`
layout into `(new quotient, old remainders, new remainder)`. -/
def stepOutputIndex
    (inputWidth base digits : Nat) :
    Fin (inputWidth + (digits + 1) * base) ->
      Fin ((inputWidth + base) + digits * base) :=
  fun output =>
    if quotient : output.val < inputWidth then
      ⟨output.val, by omega⟩
    else if retained : output.val < inputWidth + digits * base then
      ⟨output.val + base, by
        have outputBound := output.isLt
        omega⟩
    else
      ⟨inputWidth + (output.val - (inputWidth + digits * base)), by
        have outputBound : output.val <
            inputWidth + (digits * base + base) := by
          simpa [Nat.succ_mul] using output.isLt
        omega⟩

/-- Output index of an already retained remainder bit. -/
def retainedOutputIndex
    (inputWidth base digits : Nat)
    (bit : Fin (digits * base)) :
    Fin (inputWidth + (digits + 1) * base) :=
  ⟨inputWidth + bit.val, by
    rw [Nat.succ_mul]
    omega⟩

/-- Output index of a newly appended remainder bit. -/
def newRemainderOutputIndex
    (inputWidth base digits : Nat)
    (candidate : Fin base) :
    Fin (inputWidth + (digits + 1) * base) :=
  ⟨inputWidth + digits * base + candidate.val, by
    rw [Nat.succ_mul]
    omega⟩

theorem stepOutputIndex_quotient
    (bit : Fin inputWidth) :
    stepOutputIndex inputWidth base digits
        (Fin.castAdd ((digits + 1) * base) bit) =
      ⟨bit.val, by omega⟩ := by
  unfold stepOutputIndex
  split
  · apply Fin.ext
    rfl
  · rename_i notQuotient
    exact False.elim (notQuotient bit.isLt)

theorem stepOutputIndex_retained
    (bit : Fin (digits * base)) :
    stepOutputIndex inputWidth base digits
        (retainedOutputIndex inputWidth base digits bit) =
      ⟨inputWidth + base + bit.val, by omega⟩ := by
  unfold stepOutputIndex retainedOutputIndex
  simp only
  split
  · rename_i quotient
    omega
  · split
    · apply Fin.ext
      simp
      omega
    · rename_i notRetained
      omega

theorem stepOutputIndex_newRemainder
    (candidate : Fin base) :
    stepOutputIndex inputWidth base digits
        (newRemainderOutputIndex inputWidth base digits candidate) =
      ⟨inputWidth + candidate.val, by omega⟩ := by
  unfold stepOutputIndex newRemainderOutputIndex
  simp only
  split
  · rename_i quotient
    omega
  · split
    · rename_i retained
      omega
    · apply Fin.ext
      simp

/-- One repeated-conversion step.  The existing remainder log is retained at
zero cost. -/
noncomputable def stepCircuit
    (inputWidth : Nat)
    (basePositive : 0 < base)
    (digits : Nat) :
    Circuit DeMorgan.signature (inputWidth + digits * base)
      (inputWidth + (digits + 1) * base) :=
  let divide :=
    (FixedDivision.circuit inputWidth basePositive).mapInputs
      (quotientInputIndex inputWidth (digits * base))
  let retained : Circuit DeMorgan.signature
      (inputWidth + digits * base) (digits * base) :=
    (Circuit.id DeMorgan.signature
      (inputWidth + digits * base)).mapOutputs
        (retainedInputIndex inputWidth (digits * base))
  (divide.parallel retained).mapOutputs
    (stepOutputIndex inputWidth base digits) |>.castCounts rfl rfl

@[simp] theorem stepCircuit_size
    (inputWidth : Nat)
    (basePositive : 0 < base)
    (digits : Nat) :
    (stepCircuit inputWidth basePositive digits).size =
      FixedDivision.prefixGateCount inputWidth basePositive inputWidth := by
  simp [stepCircuit]

@[simp] theorem stepCircuit_eval_quotient
    (basePositive : 0 < base)
    (input : Fin (inputWidth + digits * base) -> Bool)
    (bit : Fin inputWidth) :
    (stepCircuit inputWidth basePositive digits).eval
        DeMorgan.interpretation input
        (Fin.castAdd ((digits + 1) * base) bit) =
      (FixedDivision.circuit inputWidth basePositive).eval
        DeMorgan.interpretation
        (fun source => input (Fin.castAdd (digits * base) source))
        (Fin.castAdd base bit) := by
  rw [stepCircuit, Circuit.eval_castCounts, Circuit.eval_mapOutputs]
  simp only [Fin.cast_refl, Function.comp_id, Function.comp_apply, id_eq]
  rw [stepOutputIndex_quotient]
  rw [Circuit.eval_parallel]
  rw [show (⟨bit.val, by omega⟩ :
      Fin ((inputWidth + base) + digits * base)) =
      Fin.castAdd (digits * base) (Fin.castAdd base bit) by
    apply Fin.ext
    rfl]
  rw [Fin.append_left, Circuit.eval_mapInputs]
  rfl

@[simp] theorem stepCircuit_eval_retained
    (basePositive : 0 < base)
    (input : Fin (inputWidth + digits * base) -> Bool)
    (bit : Fin (digits * base)) :
    (stepCircuit inputWidth basePositive digits).eval
        DeMorgan.interpretation input
        (retainedOutputIndex inputWidth base digits bit) =
      input (Fin.natAdd inputWidth bit) := by
  rw [stepCircuit, Circuit.eval_castCounts, Circuit.eval_mapOutputs]
  simp only [Fin.cast_refl, Function.comp_id, Function.comp_apply, id_eq]
  rw [stepOutputIndex_retained]
  rw [Circuit.eval_parallel]
  rw [show (⟨inputWidth + base + bit.val, by omega⟩ :
      Fin ((inputWidth + base) + digits * base)) =
      Fin.natAdd (inputWidth + base) bit by
    apply Fin.ext
    rfl]
  rw [Fin.append_right, Circuit.eval_mapOutputs, Circuit.eval_id]
  rfl

@[simp] theorem stepCircuit_eval_newRemainder
    (basePositive : 0 < base)
    (input : Fin (inputWidth + digits * base) -> Bool)
    (candidate : Fin base) :
    (stepCircuit inputWidth basePositive digits).eval
        DeMorgan.interpretation input
        (newRemainderOutputIndex inputWidth base digits candidate) =
      (FixedDivision.circuit inputWidth basePositive).eval
        DeMorgan.interpretation
        (fun source => input (Fin.castAdd (digits * base) source))
        (Fin.natAdd inputWidth candidate) := by
  rw [stepCircuit, Circuit.eval_castCounts, Circuit.eval_mapOutputs]
  simp only [Fin.cast_refl, Function.comp_id, Function.comp_apply, id_eq]
  rw [stepOutputIndex_newRemainder]
  rw [Circuit.eval_parallel]
  rw [show (⟨inputWidth + candidate.val, by omega⟩ :
      Fin ((inputWidth + base) + digits * base)) =
      Fin.castAdd (digits * base)
        (Fin.natAdd inputWidth candidate) by
    apply Fin.ext
    rfl]
  rw [Fin.append_left, Circuit.eval_mapInputs]
  rfl

/-- Repeated fixed-base conversion circuit. -/
noncomputable def circuit
    (inputWidth : Nat)
    (basePositive : 0 < base) :
    (digits : Nat) ->
    Circuit DeMorgan.signature inputWidth
      (inputWidth + digits * base)
  | 0 => (Circuit.id DeMorgan.signature inputWidth).castCounts rfl
      (by simp)
  | digits + 1 =>
      ((stepCircuit inputWidth basePositive digits).comp
        (circuit inputWidth basePositive digits)).castCounts rfl rfl

/-- Repeated conversion emits exactly `gateCount` gates. -/
@[simp] theorem circuit_size
    (inputWidth : Nat)
    (basePositive : 0 < base)
    (digits : Nat) :
    (circuit inputWidth basePositive digits).size =
      gateCount inputWidth basePositive digits := by
  induction digits with
  | zero => simp [circuit, gateCount]
  | succ digits inductionHypothesis =>
      simp [circuit, gateCount, inductionHypothesis, stepCircuit]

/-- Natural quotient represented by the current quotient block. -/
def quotientValue
    (input : Fin inputWidth -> Bool)
    (base digits : Nat) : Nat :=
  (FixedDivision.bitVectorIndex input).val / base ^ digits

/-- The `digit`th least-significant base digit, as a bounded index. -/
def digitValue
    (basePositive : 0 < base)
    (input : Fin inputWidth -> Bool)
    (digit : Nat) : Fin base :=
  ⟨(FixedDivision.bitVectorIndex input).val / base ^ digit % base,
    Nat.mod_lt _ basePositive⟩

/-- The current quotient block has value `input / base^digits`. -/
theorem circuit_quotient_value
    (basePositive : 0 < base)
    (input : Fin inputWidth -> Bool)
    (digits : Nat) :
    (FixedDivision.bitVectorIndex fun bit =>
      (circuit inputWidth basePositive digits).eval
        DeMorgan.interpretation input
        (Fin.castAdd (digits * base) bit)).val =
      quotientValue input base digits := by
  induction digits with
  | zero =>
      rw [circuit, Circuit.eval_castCounts]
      simp only [Fin.cast_refl, Function.comp_id, Circuit.eval_id]
      rw [show (fun bit =>
          input (Fin.cast (by simp : inputWidth + 0 * base = inputWidth)
        (Fin.castAdd (0 * base) bit))) = input by
        funext bit
        congr 1]
      simp [quotientValue]
  | succ priorDigits inductionHypothesis =>
      rw [circuit, Circuit.eval_castCounts]
      simp only [Fin.cast_refl, Function.comp_id, Circuit.eval_comp, id_eq]
      rw [show (fun bit =>
          (stepCircuit inputWidth basePositive priorDigits).eval
            DeMorgan.interpretation
            ((circuit inputWidth basePositive priorDigits).eval
              DeMorgan.interpretation input)
            (Fin.castAdd ((priorDigits + 1) * base) bit)) =
          fun bit =>
            (FixedDivision.circuit inputWidth basePositive).eval
              DeMorgan.interpretation
              (fun source =>
                (circuit inputWidth basePositive priorDigits).eval
                  DeMorgan.interpretation input
                  (Fin.castAdd (priorDigits * base) source))
              (Fin.castAdd base bit) by
        funext bit
        exact stepCircuit_eval_quotient basePositive _ bit]
      rw [FixedDivision.circuit_quotient_value]
      rw [inductionHypothesis]
      unfold quotientValue
      rw [Nat.pow_succ, ← Nat.div_div_eq_div_mul]

/-- Every emitted remainder block is one-hot at the corresponding base
digit. -/
theorem circuit_digit_oneHot
    (basePositive : 0 < base)
    (input : Fin inputWidth -> Bool)
    (digits : Nat)
    (digit : Fin digits)
    (candidate : Fin base) :
    (circuit inputWidth basePositive digits).eval
        DeMorgan.interpretation input
        (Fin.natAdd inputWidth (finProdFinEquiv (digit, candidate))) =
      decide (candidate = digitValue basePositive input digit.val) := by
  induction digits with
  | zero => exact Fin.elim0 digit
  | succ priorDigits inductionHypothesis =>
      rw [circuit, Circuit.eval_castCounts]
      simp only [Fin.cast_refl, Function.comp_id, Circuit.eval_comp, id_eq]
      induction digit using Fin.lastCases with
      | last =>
          rw [show Fin.natAdd inputWidth (finProdFinEquiv
                (Fin.last priorDigits, candidate)) =
              newRemainderOutputIndex inputWidth base priorDigits candidate by
            apply Fin.ext
            simp [finProdFinEquiv, newRemainderOutputIndex]
            ring]
          rw [stepCircuit_eval_newRemainder]
          rw [FixedDivision.circuit_remainder_oneHot]
          unfold FixedDivision.remainder digitValue
          apply congrArg
            (fun selected : Fin base => decide (candidate = selected))
          apply Fin.ext
          change
            (FixedDivision.bitVectorIndex fun source =>
              (circuit inputWidth basePositive priorDigits).eval
                DeMorgan.interpretation input
                (Fin.castAdd (priorDigits * base) source)).val % base =
              (FixedDivision.bitVectorIndex input).val /
                base ^ priorDigits % base
          rw [circuit_quotient_value]
          rfl
      | cast priorDigit =>
          rw [show Fin.natAdd inputWidth (finProdFinEquiv
                (priorDigit.castSucc, candidate)) =
              retainedOutputIndex inputWidth base priorDigits
                (finProdFinEquiv (priorDigit, candidate)) by
            apply Fin.ext
            simp [finProdFinEquiv, retainedOutputIndex]]
          rw [stepCircuit_eval_retained]
          simpa using inductionHypothesis priorDigit

@[simp] theorem stepCircuit_cost
    (basePositive : 0 < base)
    (digits : Nat) :
    (stepCircuit inputWidth basePositive digits).cost
        DeMorgan.standardCost =
      (FixedDivision.circuit inputWidth basePositive).cost
        DeMorgan.standardCost := by
  simp [stepCircuit]

/-- Repeated conversion charges exactly one divider per emitted digit. -/
theorem circuit_cost
    (basePositive : 0 < base)
    (digits : Nat) :
    (circuit inputWidth basePositive digits).cost DeMorgan.standardCost =
      digits * (FixedDivision.circuit inputWidth basePositive).cost
        DeMorgan.standardCost := by
  induction digits with
  | zero => simp [circuit]
  | succ digits inductionHypothesis =>
      rw [circuit, Circuit.cost_castCounts, Circuit.cost_comp,
        stepCircuit_cost, inductionHypothesis]
      ring

/-- Coarse explicit cost bound for `digits` base digits. -/
theorem circuit_cost_le
    (basePositive : 0 < base)
    (digits : Nat) :
    (circuit inputWidth basePositive digits).cost DeMorgan.standardCost <=
      digits * (inputWidth * (8 * base)) := by
  rw [circuit_cost]
  exact Nat.mul_le_mul_left digits
    (FixedDivision.circuit_cost_le basePositive)

end BaseConversion
end MassProduction
end Algebraic
