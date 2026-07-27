/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.Encoding.Machine.Core.Internal.Execution.Family
public import Complexitylib.Models.TuringMachine.Hoare

/-!
# Hoare contract for the serialized-family evaluator core

This file packages the total frontier execution theorem behind the public
staged-tape precondition and defaulted-verdict postcondition.
-/

@[expose] public section

namespace Complexity

namespace CircuitCode

namespace Machine

namespace Internal

/-- Internal proof of the uniform quadratic core contract. -/
theorem evalFamilyCoreTM_hoareTime_internal (codeBits inputBits : List Bool)
    (initialInput : Tape) :
    evalFamilyCoreTM.HoareTime
      (FamilyCorePre codeBits inputBits initialInput)
      (FamilyCorePost codeBits inputBits initialInput)
      (evalFamilyCoreTime codeBits.length inputBits.length) := by
  intro inp work out hpre
  rcases hpre with ⟨hinp, hinput, hcode0, hcode, hwires0, hwires,
    hcounter, houtputHead, houtputInv⟩
  subst inp
  have hcodeCursor := BinaryCursor.ofHasBinaryPrefix hcode hcode0
  have hwiresCursor := BinaryCursor.ofHasBinaryPrefix hwires hwires0
  have hcounterPrefix : (work counterIdx).HasUnaryPrefix 0 := by
    rw [hcounter]
    exact Tape.init_nil_move_right_hasUnaryPrefix_zero
  have hcounter0 : (work counterIdx).cells 0 = Γ.start := by
    rw [hcounter]
    simp [Tape.init, Tape.move]
  obtain ⟨t, code', wires', counter', output', ht, hrun, houtput'Head,
      houtput'Inv, houtput'Cell⟩ :=
    familyCore_fromFrontiers_run codeBits inputBits initialInput
      (work codeIdx) (work wiresIdx) (work counterIdx) out hcodeCursor
      hwiresCursor hcounterPrefix hcounter0 hinput houtputHead houtputInv
  refine ⟨coreCfg .done initialInput code' wires' counter' output', t, ht,
    ?_, ?_, ?_⟩
  · have hstart :
        coreCfg .rewindCode initialInput (work codeIdx) (work wiresIdx)
            (work counterIdx) out =
          { state := evalFamilyCoreTM.qstart
            input := initialInput
            work := work
            output := out } := by
      exact Cfg.ext rfl rfl (coreWork_eta work) rfl
    rw [← hstart]
    exact hrun
  · rfl
  · exact ⟨rfl, houtput'Head, houtput'Inv, houtput'Cell⟩

end Internal

end Machine

end CircuitCode

end Complexity
