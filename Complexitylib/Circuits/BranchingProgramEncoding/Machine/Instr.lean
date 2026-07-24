/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Circuits.BranchingProgramEncoding.Machine.Instr.Defs
import Complexitylib.Circuits.BranchingProgramEncoding.Machine.Instr.Internal

/-!
# Machine emission of width-five branching-program instructions

This module exposes the serializer leaf used by the machine-level Barrington
generator.  A canonical binary variable register is emitted in terminated unary,
followed by the two fixed seven-bit permutation ranks.  The input and complete
work frame are restored literally.
-/

namespace Complexity

namespace BPCode

namespace Machine

open TM

variable {n : ℕ}

/-- Emit one complete instruction code from a preserved binary variable
register and two finite-control permutations. -/
theorem emitInstrTM_hoareTime
    (counterIdx varIdx : Fin n) (hne : counterIdx ≠ varIdx)
    (varValue : ℕ) (perm0 perm1 : Equiv.Perm (Fin 5))
    (inp₀ : Tape) (work₀ : Fin n → Tape) (ys : List Bool)
    (hinp : Parked inp₀)
    (hcounter : (work₀ counterIdx).HasBinaryNat 0)
    (hvar : (work₀ varIdx).HasBinaryNat varValue)
    (hother : ∀ i, i ≠ counterIdx → i ≠ varIdx → Parked (work₀ i)) :
    (emitInstrTM counterIdx varIdx perm0 perm1).HoareTime
      (EmitPred inp₀ work₀ ys)
      (EmitPred inp₀ work₀
        (ys ++ Instr.encode
          { var := varValue, perm0 := perm0, perm1 := perm1 }))
      (emitInstrTime varValue) :=
  emitInstrTM_hoareTime_internal counterIdx varIdx hne varValue perm0 perm1
    inp₀ work₀ ys hinp hcounter hvar hother

/-- Time-and-space form of `emitInstrTM_hoareTime`. -/
theorem emitInstrTM_hoareTimeSpace
    (counterIdx varIdx : Fin n) (hne : counterIdx ≠ varIdx)
    (varValue inputLength initialSpace : ℕ)
    (perm0 perm1 : Equiv.Perm (Fin 5))
    (inp₀ : Tape) (work₀ : Fin n → Tape) (ys : List Bool)
    (hinp : Parked inp₀)
    (hcounter : (work₀ counterIdx).HasBinaryNat 0)
    (hvar : (work₀ varIdx).HasBinaryNat varValue)
    (hother : ∀ i, i ≠ counterIdx → i ≠ varIdx → Parked (work₀ i))
    (hworkSpace : ∀ i, (work₀ i).head ≤ initialSpace)
    (hinputSpace : inp₀.head ≤ inputLength + initialSpace + 1) :
    (emitInstrTM counterIdx varIdx perm0 perm1).HoareTimeSpace
      (EmitPred inp₀ work₀ ys)
      (EmitPred inp₀ work₀
        (ys ++ Instr.encode
          { var := varValue, perm0 := perm0, perm1 := perm1 }))
      (emitInstrTime varValue) inputLength
      (emitInstrSpace initialSpace varValue) :=
  emitInstrTM_hoareTimeSpace_internal counterIdx varIdx hne varValue
    inputLength initialSpace perm0 perm1 inp₀ work₀ ys hinp hcounter hvar
    hother hworkSpace hinputSpace

/-- Instruction emission never moves its output head left. -/
theorem emitInstrTM_isTransducer
    (counterIdx varIdx : Fin n) (perm0 perm1 : Equiv.Perm (Fin 5)) :
    (emitInstrTM counterIdx varIdx perm0 perm1).IsTransducer :=
  emitInstrTM_isTransducer_internal counterIdx varIdx perm0 perm1

/-- The constant-leaf specialization emits exactly `BPInstr.const target`. -/
theorem emitConstInstrTM_hoareTime
    (counterIdx zeroIdx : Fin n) (hne : counterIdx ≠ zeroIdx)
    (target : Equiv.Perm (Fin 5))
    (inp₀ : Tape) (work₀ : Fin n → Tape) (ys : List Bool)
    (hinp : Parked inp₀)
    (hcounter : (work₀ counterIdx).HasBinaryNat 0)
    (hzero : (work₀ zeroIdx).HasBinaryNat 0)
    (hother : ∀ i, i ≠ counterIdx → i ≠ zeroIdx → Parked (work₀ i)) :
    (emitConstInstrTM counterIdx zeroIdx target).HoareTime
      (EmitPred inp₀ work₀ ys)
      (EmitPred inp₀ work₀ (ys ++ Instr.encode (BPInstr.const target)))
      (emitInstrTime 0) := by
  simpa [emitConstInstrTM, BPInstr.const] using
    emitInstrTM_hoareTime counterIdx zeroIdx hne 0 target target inp₀ work₀
      ys hinp hcounter hzero hother

/-- The variable-leaf specialization emits exactly the Barrington variable
instruction with identity on zero and `target` on one. -/
theorem emitVarInstrTM_hoareTime
    (counterIdx varIdx : Fin n) (hne : counterIdx ≠ varIdx)
    (varValue : ℕ) (target : Equiv.Perm (Fin 5))
    (inp₀ : Tape) (work₀ : Fin n → Tape) (ys : List Bool)
    (hinp : Parked inp₀)
    (hcounter : (work₀ counterIdx).HasBinaryNat 0)
    (hvar : (work₀ varIdx).HasBinaryNat varValue)
    (hother : ∀ i, i ≠ counterIdx → i ≠ varIdx → Parked (work₀ i)) :
    (emitVarInstrTM counterIdx varIdx target).HoareTime
      (EmitPred inp₀ work₀ ys)
      (EmitPred inp₀ work₀
        (ys ++ Instr.encode ⟨varValue, 1, target⟩))
      (emitInstrTime varValue) := by
  simpa [emitVarInstrTM] using
    emitInstrTM_hoareTime counterIdx varIdx hne varValue 1 target inp₀ work₀
      ys hinp hcounter hvar hother

end Machine

end BPCode

end Complexity
