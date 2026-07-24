/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Circuits.BarringtonStreaming.Defs
import Complexitylib.Circuits.BarringtonCompiler

/-!
# Random-access Barrington instruction streams -- proof internals
-/

namespace Complexity

namespace BPStream

theorem empty_correctFor_internal :
    (empty : BPStream w).CorrectFor [] := by
  simp [CorrectFor, empty]

theorem singleton_correctFor_internal (instruction : BPInstr w) :
    (singleton instruction).CorrectFor [instruction] := by
  constructor
  · rfl
  · intro index
    cases index <;> simp [singleton]

theorem CorrectFor.append_internal {left right : BPStream w}
    {leftProgram rightProgram : BP w}
    (hleft : left.CorrectFor leftProgram)
    (hright : right.CorrectFor rightProgram) :
    (left.append right).CorrectFor (leftProgram ++ rightProgram) := by
  constructor
  · simp [append, hleft.1, hright.1]
  · intro index
    rw [append]
    dsimp only
    rw [hleft.1]
    by_cases hindex : index < leftProgram.length
    · rw [if_pos hindex, hleft.2, List.getElem?_append_left hindex]
    · rw [if_neg hindex, hright.2,
        List.getElem?_append_right (by omega)]

theorem CorrectFor.inverse_internal {stream : BPStream w}
    {program : BP w} (hstream : stream.CorrectFor program) :
    stream.inverse.CorrectFor program.inverse := by
  constructor
  · simp [inverse, BP.inverse, hstream.1]
  · intro index
    rw [inverse]
    dsimp only
    rw [hstream.1]
    by_cases hindex : index < program.length
    · rw [if_pos hindex, hstream.2]
      simp only [BP.inverse]
      rw [List.getElem?_reverse (by simpa using hindex),
        List.getElem?_map]
      simp
    · rw [if_neg hindex]
      simp [BP.inverse, hindex]

theorem CorrectFor.postMul_internal {stream : BPStream w}
    {program : BP w} (hstream : stream.CorrectFor program)
    (permutation : Equiv.Perm (Fin w)) :
    (stream.postMul permutation).CorrectFor
      (BP.postMul program permutation) := by
  constructor
  · simpa [postMul, hstream.1] using
      (BP.length_postMul program permutation).symm
  · intro index
    induction program using List.reverseRecOn with
    | nil =>
        have hlength : stream.length = 0 := by simpa using hstream.1
        change (if stream.length = 0 then
          if index = 0 then some (BPInstr.const permutation) else none
        else if index + 1 = stream.length then
          (stream.instruction? index).map fun instruction =>
            BPInstr.postMul instruction permutation
        else stream.instruction? index) = _
        rw [hlength]
        cases index <;> simp [BP.postMul]
    | append_singleton program last ih =>
        have hlength : stream.length = program.length + 1 := by
          simpa using hstream.1
        change (if stream.length = 0 then
          if index = 0 then some (BPInstr.const permutation) else none
        else if index + 1 = stream.length then
          (stream.instruction? index).map fun instruction =>
            BPInstr.postMul instruction permutation
        else stream.instruction? index) = _
        rw [if_neg (by omega : stream.length ≠ 0)]
        have hpost : BP.postMul (program ++ [last]) permutation =
            program ++ [BPInstr.postMul last permutation] := by
          simp [BP.postMul, List.modifyLast_concat]
        rw [hpost]
        by_cases hbefore : index < program.length
        · rw [if_neg (by omega : index + 1 ≠ stream.length)]
          rw [hstream.2, List.getElem?_append_left hbefore,
            List.getElem?_append_left hbefore]
        · by_cases hlast : index = program.length
          · subst index
            rw [if_pos (by omega : program.length + 1 = stream.length)]
            simp [hstream.2]
          · have hpast : program.length + 1 ≤ index := by omega
            rw [if_neg (by omega : index + 1 ≠ stream.length)]
            rw [hstream.2]
            simp [List.getElem?_eq_none, hpast]

theorem CorrectFor.commutator_internal {left right : BPStream w}
    {leftProgram rightProgram : BP w}
    (hleft : left.CorrectFor leftProgram)
    (hright : right.CorrectFor rightProgram) :
    (commutator left right).CorrectFor
      (BP.commutatorProgram leftProgram rightProgram) := by
  exact (((hleft.append_internal hright).append_internal
    hleft.inverse_internal).append_internal hright.inverse_internal)

end BPStream

/-- Internal exact instruction-count recurrence. -/
theorem barringtonInstructionCount_eq_length_internal
    (formula : BoolFormula) (target : Equiv.Perm (Fin 5)) :
    barringtonInstructionCount formula =
      (barringtonCompile formula target).length := by
  induction formula generalizing target with
  | var index => rfl
  | tru => rfl
  | fls => rfl
  | neg formula ih =>
      simp only [barringtonInstructionCount, barringtonCompile,
        BP.length_postMul]
      rw [← ih target⁻¹]
  | conj left right ihLeft ihRight =>
      simp only [barringtonInstructionCount, barringtonCompile,
        BP.length_commutatorProgram]
      rw [← ihLeft (barringtonLeft target),
        ← ihRight (barringtonRight target)]
  | disj left right ihLeft ihRight =>
      simp only [barringtonInstructionCount, barringtonCompile,
        BP.length_postMul, BP.length_commutatorProgram]
      rw [← ihLeft (barringtonLeft target⁻¹)⁻¹,
        ← ihRight (barringtonRight target⁻¹)⁻¹]
      omega

/-- Internal exactness of the random-access compiler. -/
theorem barringtonCompileStream_correctFor_internal
    (formula : BoolFormula) (target : Equiv.Perm (Fin 5)) :
    (barringtonCompileStream formula target).CorrectFor
      (barringtonCompile formula target) := by
  induction formula generalizing target with
  | var index =>
      exact BPStream.singleton_correctFor_internal _
  | tru =>
      exact BPStream.singleton_correctFor_internal _
  | fls =>
      exact BPStream.empty_correctFor_internal
  | neg formula ih =>
      exact (ih target⁻¹).postMul_internal target
  | conj left right ihLeft ihRight =>
      exact BPStream.CorrectFor.commutator_internal
        (ihLeft (barringtonLeft target))
        (ihRight (barringtonRight target))
  | disj left right ihLeft ihRight =>
      let innerTarget := target⁻¹
      let leftTarget := barringtonLeft innerTarget
      let rightTarget := barringtonRight innerTarget
      let leftStream :=
        (barringtonCompileStream left leftTarget⁻¹).postMul leftTarget
      let rightStream :=
        (barringtonCompileStream right rightTarget⁻¹).postMul rightTarget
      let leftProgram := BP.postMul
        (barringtonCompile left leftTarget⁻¹) leftTarget
      let rightProgram := BP.postMul
        (barringtonCompile right rightTarget⁻¹) rightTarget
      have hleft : leftStream.CorrectFor leftProgram :=
        (ihLeft leftTarget⁻¹).postMul_internal leftTarget
      have hright : rightStream.CorrectFor rightProgram :=
        (ihRight rightTarget⁻¹).postMul_internal rightTarget
      exact (hleft.commutator_internal hright).postMul_internal target

end Complexity
