/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Circuits.BranchingProgramEncoding
import Complexitylib.Circuits.BranchingProgramEncoding.Machine.Instr.Defs
import Complexitylib.Circuits.Encoding.Machine.NatCode
import Complexitylib.Models.TuringMachine.Hoare.Space

/-!
# Machine emission of width-five branching-program instructions -- proof internals
-/

namespace Complexity

namespace BPCode

namespace Machine

open TM
open CircuitCode.Machine

variable {n : ℕ}

private theorem instrInitialWork_parked
    (counterIdx varIdx : Fin n) (work₀ : Fin n → Tape) (varValue : ℕ)
    (hcounter : (work₀ counterIdx).HasBinaryNat 0)
    (hvar : (work₀ varIdx).HasBinaryNat varValue)
    (hother : ∀ i, i ≠ counterIdx → i ≠ varIdx → Parked (work₀ i)) :
    ∀ i, Parked (work₀ i) := by
  intro i
  by_cases hic : i = counterIdx
  · subst i
    refine ⟨by rw [hcounter.2.1], ?_⟩
    exact Tape.HasBinaryContent.cells_ne_start hcounter.2.2
  by_cases hiv : i = varIdx
  · subst i
    refine ⟨by rw [hvar.2.1], ?_⟩
    exact Tape.HasBinaryContent.cells_ne_start hvar.2.2
  · exact hother i hic hiv

theorem emitInstrTM_hoareTime_internal
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
      (emitInstrTime varValue) := by
  have hwork := instrInitialWork_parked counterIdx varIdx work₀ varValue
    hcounter hvar hother
  have hrun := seqTM_hoareTime
    (emitNatCodeTM counterIdx varIdx)
    (emitBitsTM (Perm5.encode perm0 ++ Perm5.encode perm1))
    (emitNatCodeTM_hoareTime counterIdx varIdx hne varValue inp₀ work₀ ys
      hinp hcounter hvar (fun i _ _ => hwork i))
    (emitPred_transition hinp hwork (ys ++ CircuitCode.NatCode.encode varValue))
    (emitBitsTM_hoareTime (Perm5.encode perm0 ++ Perm5.encode perm1)
      inp₀ work₀ (ys ++ CircuitCode.NatCode.encode varValue) hinp hwork)
  refine hrun.consequence (fun _ _ _ h => h) (fun inp work out h => ?_) ?_
  · simpa [Instr.encode, List.append_assoc] using h
  · simp [emitInstrTime, Perm5.bitWidth]

theorem emitInstrTM_hoareTimeSpace_internal
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
      (emitInstrSpace initialSpace varValue) := by
  have hwork := instrInitialWork_parked counterIdx varIdx work₀ varValue
    hcounter hvar hother
  have htailTime :=
    emitBitsTM_hoareTime (Perm5.encode perm0 ++ Perm5.encode perm1)
      inp₀ work₀ (ys ++ CircuitCode.NatCode.encode varValue) hinp hwork
  have htail := htailTime.toHoareTimeSpace (fun inp work out h => by
    rcases h with ⟨rfl, rfl, -⟩
    exact ⟨hworkSpace, hinputSpace⟩)
  have hrun := seqTM_hoareTimeSpace
    (emitNatCodeTM counterIdx varIdx)
    (emitBitsTM (Perm5.encode perm0 ++ Perm5.encode perm1))
    (emitNatCodeTM_hoareTimeSpace counterIdx varIdx hne varValue inputLength
      initialSpace inp₀ work₀ ys hinp hcounter hvar
      (fun i _ _ => hwork i) hworkSpace hinputSpace)
    (emitPred_transition hinp hwork (ys ++ CircuitCode.NatCode.encode varValue))
    htail
  refine hrun.consequence (fun _ _ _ h => h) (fun inp work out h => ?_)
    ?_ le_rfl ?_
  · simpa [Instr.encode, List.append_assoc] using h
  · simp [emitInstrTime, Perm5.bitWidth]
  · simp only [emitInstrSpace, emitNatCodeSpace, Perm5.length_encode,
      Perm5.bitWidth, List.length_append]
    apply max_le <;> omega

theorem emitInstrTM_isTransducer_internal
    (counterIdx varIdx : Fin n) (perm0 perm1 : Equiv.Perm (Fin 5)) :
    (emitInstrTM counterIdx varIdx perm0 perm1).IsTransducer := by
  exact (emitNatCodeTM_isTransducer counterIdx varIdx).seqTM
    (emitBitsTM_isTransducer (Perm5.encode perm0 ++ Perm5.encode perm1))

end Machine

end BPCode

end Complexity
