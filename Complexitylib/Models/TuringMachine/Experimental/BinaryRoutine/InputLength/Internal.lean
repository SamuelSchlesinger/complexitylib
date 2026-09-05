/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Models.TuringMachine.Experimental.BinaryRoutine
public import Complexitylib.Models.TuringMachine.Experimental.BinaryRoutine.InputLength.Defs
public import Complexitylib.Models.TuringMachine.Subroutines.BinaryLength

/-!
# Fresh-input entry for proof-carrying binary routines -- proof internals
-/


public section

namespace Complexity

namespace BinaryRoutine

variable {n : ℕ}

private theorem work_after_binaryLength (lengthIdx : Fin n) (length : ℕ)
    (work : Fin n → Tape)
    (htarget : (work lengthIdx).HasBinaryNat length)
    (hother : ∀ i, i ≠ lengthIdx →
      work i = (Tape.init []).move Dir3.right) :
    work = workTapes (inputLengthValues lengthIdx length) := by
  funext i
  by_cases hi : i = lengthIdx
  · subst i
    rw [htarget.eq_init_move_right]
    simp [workTapes, inputLengthValues, natTape]
  · rw [hother i hi]
    simp [workTapes, inputLengthValues, natTape, hi]

private theorem input_after_binaryLength_parked (input : Tape)
    (cells : ℕ → Γ) (length : ℕ)
    (hinputCells : input.cells = cells)
    (hinputHead : input.head = length + 1)
    (hsource : TM.Parked { head := 1, cells := cells }) :
    TM.Parked input := by
  constructor
  · rw [hinputHead]
    omega
  · intro j hj
    rw [hinputCells]
    exact hsource.2 j (by omega)

theorem Sound.afterInputLength_hoareTimeSpace_internal
    {routine : BinaryRoutine n} (hsound : routine.Sound)
    (lengthIdx : Fin n) (input : List Bool)
    (hrequires : routine.requires
      (inputLengthValues lengthIdx input.length)) :
    (afterInputLength lengthIdx routine).HoareTimeSpace
      (fun inp work out =>
        inp = Tape.init (input.map Γ.ofBool) ∧
        work = (fun _ => Tape.init []) ∧ out = Tape.init [])
      (fun _ _ out => out.HasOutput
        (afterInputLengthFunction lengthIdx routine input))
      (afterInputLengthTime lengthIdx routine input.length) input.length
      (afterInputLengthSpace lengthIdx routine input.length) := by
  let values := inputLengthValues lengthIdx input.length
  let inp₁ : Tape :=
    { head := input.length + 1
      cells := (Tape.init (input.map Γ.ofBool)).cells }
  have hinp₁ : TM.Parked inp₁ := by
    apply input_after_binaryLength_parked inp₁
      (Tape.init (input.map Γ.ofBool)).cells input.length
    · rfl
    · rfl
    · exact TM.parked_init_input input
  have hlengthSpace : 1 ≤ TM.binaryLengthSpace input.length := by
    simp [TM.binaryLengthSpace]
  have hinputSpace :
      inp₁.head ≤ input.length + TM.binaryLengthSpace input.length + 1 := by
    dsimp only [inp₁]
    omega
  have hleft := TM.binaryLengthTM_hoareTimeSpace lengthIdx input
  have hright := hsound.hoareTimeSpace values inp₁ [] input.length
    (TM.binaryLengthSpace input.length) hrequires hinp₁ hlengthSpace
    hinputSpace
  have hseq :
      (afterInputLength lengthIdx routine).HoareTimeSpace
        (fun inp work out =>
          inp = Tape.init (input.map Γ.ofBool) ∧
          work = (fun _ => Tape.init []) ∧ out = Tape.init [])
        (CanonicalPred inp₁ (routine.effect values)
          (routine.emitted values))
        (afterInputLengthTime lengthIdx routine input.length) input.length
        (afterInputLengthSpace lengthIdx routine input.length) := by
    apply TM.seqTM_hoareTimeSpace
      (TM.binaryLengthTM lengthIdx) routine.machine hleft
    · intro inp work out hpost
      rcases hpost with
        ⟨hinputCells, hinputHead, htarget, hother, houtput⟩
      have hinput : inp = inp₁ := by
        apply Tape.ext
        · exact hinputHead
        · exact hinputCells
      have hwork : work = workTapes values := by
        apply work_after_binaryLength lengthIdx input.length
        · exact htarget
        · exact hother
      have houtAcc : TM.OutAcc [] out := by
        rw [houtput]
        exact TM.outAcc_nil_init
      have hcanonical : CanonicalPred inp₁ values [] inp work out := by
        exact ⟨hinput, hwork, houtAcc⟩
      exact TM.emitPred_transition hinp₁ (workTapes_parked values) []
        inp work out hcanonical
    · exact hright
  apply hseq.consequence
  · exact fun _ _ _ hpre => hpre
  · intro _inp _work out hpost
    exact hpost.2.2.hasOutput
  · exact le_rfl
  · exact le_rfl
  · exact le_rfl

theorem Sound.afterInputLength_computesInSpace_internal
    {routine : BinaryRoutine n} (hsound : routine.Sound)
    (lengthIdx : Fin n)
    (hrequires : ∀ length,
      routine.requires (inputLengthValues lengthIdx length)) :
    (afterInputLength lengthIdx routine).ComputesInSpace
      (afterInputLengthFunction lengthIdx routine)
      (afterInputLengthSpace lengthIdx routine) := by
  apply TM.computesInSpace_of_hoareTimeSpace
  · exact (TM.binaryLengthTM_isTransducer lengthIdx).seqTM hsound.isTransducer
  · intro input
    exact hsound.afterInputLength_hoareTimeSpace_internal lengthIdx input
      (hrequires input.length)

theorem afterInputLengthSpace_bigO_log_internal
    (lengthIdx : Fin n) (routine : BinaryRoutine n)
    (hroutine : (fun length =>
      routine.spaceBound (TM.binaryLengthSpace length)
        (inputLengthValues lengthIdx length)) =O
          (fun length => Nat.log 2 length)) :
    afterInputLengthSpace lengthIdx routine =O
      (fun length => Nat.log 2 length) := by
  unfold afterInputLengthSpace
  exact BigO.max_same TM.binaryLengthSpace_bigO_log hroutine

end BinaryRoutine

end Complexity
