/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Models.TuringMachine.Subroutines.BinaryEq.Defs
import Complexitylib.Models.TuringMachine.Hoare.Space
import Complexitylib.Models.TuringMachine.Combinators.Internal.Generic
import Complexitylib.Models.TuringMachine.Registers
import Complexitylib.Models.TuringMachine.Subroutines.ClearWork.Internal
import Complexitylib.Models.TuringMachine.Subroutines.ResetBinary.Internal

/-!
# Binary work-tape equality — proof internals
-/

namespace Complexity

namespace TM

private theorem parked_of_hasBinaryPrefix {t : Tape} {bits : List Bool}
    (h : t.HasBinaryPrefix bits) : Parked t :=
  ⟨by rw [h.1]; omega,
    Tape.HasBinaryContent.cells_ne_start
      (show t.HasBinaryContent bits from h.2)⟩

private theorem parked_of_hasBinaryContent {t : Tape} {bits : List Bool}
    (h : t.HasBinaryContent bits) (hhead : 1 ≤ t.head) : Parked t :=
  ⟨hhead, h.cells_ne_start⟩

private def binaryEqResultWork {n : ℕ} (resultIdx : Fin n)
    (work : Fin n → Tape) (result : Bool) : Fin n → Tape :=
  Function.update work resultIdx
    ((work resultIdx).writeAndMove (Γw.ofBool result) Dir3.right)

private def binaryEqAdvanceWork {n : ℕ} (lhsIdx rhsIdx : Fin n)
    (work : Fin n → Tape) : Fin n → Tape :=
  fun i => if i = lhsIdx then (work i).move Dir3.right
    else if i = rhsIdx then (work i).move Dir3.right else work i

private def binaryEqResultCfg {n : ℕ} (resultIdx : Fin n)
    (result : Bool) (inp : Tape) (work : Fin n → Tape) (out : Tape) :
    Cfg n BinaryEqPhase where
  state := .done
  input := inp
  work := binaryEqResultWork resultIdx work result
  output := out

private def binaryEqAdvanceCfg {n : ℕ} (lhsIdx rhsIdx : Fin n)
    (inp : Tape) (work : Fin n → Tape) (out : Tape) : Cfg n BinaryEqPhase where
  state := .scan
  input := inp
  work := binaryEqAdvanceWork lhsIdx rhsIdx work
  output := out

private theorem writeAndMove_readBack_right {tape : Tape}
    (hread : tape.read ≠ Γ.start) :
    tape.writeAndMove (readBackWrite tape.read) Dir3.right =
      tape.move Dir3.right := by
  cases tape with
  | mk head cells =>
      simp only [Tape.writeAndMove, Tape.read] at hread ⊢
      rw [toΓ_readBackWrite_of_ne_start hread]
      simp [Tape.write, Tape.move, Function.update_eq_self]

private theorem binaryEq_terminal_step {n : ℕ}
    (lhsIdx rhsIdx resultIdx : Fin n) (result : Bool)
    (inp : Tape) (work : Fin n → Tape) (out : Tape)
    (hterminal : if result then
      (work lhsIdx).read = Γ.blank ∧ (work rhsIdx).read = Γ.blank
      else ¬((work lhsIdx).read = (work rhsIdx).read))
    (hinput : inp.read ≠ Γ.start)
    (hwork : ∀ i, i ≠ resultIdx → (work i).read ≠ Γ.start)
    (houtput : out.read ≠ Γ.start) :
    (binaryEqTM lhsIdx rhsIdx resultIdx).step
      { state := .scan, input := inp, work := work, output := out } =
      some (binaryEqResultCfg resultIdx result inp work out) := by
  simp only [TM.step, binaryEqTM]
  cases result with
  | false =>
      simp only [Bool.false_eq_true, if_false] at hterminal
      have hnotBlank : ¬((work lhsIdx).read = Γ.blank ∧
          (work rhsIdx).read = Γ.blank) := by
        intro hblank
        exact hterminal (hblank.1.trans hblank.2.symm)
      rw [if_neg hnotBlank, if_neg hterminal]
      simp only [show BinaryEqPhase.scan ≠ BinaryEqPhase.done by decide,
        if_false]
      refine congrArg some (Cfg.ext rfl (transitionInput_eq_self hinput) ?_
        (transitionTape_eq_self houtput))
      funext i
      by_cases hi : i = resultIdx
      · subst i
        simp [binaryEqResultCfg, binaryEqResultWork, Γw.ofBool]
      · simpa [binaryEqResultCfg, binaryEqResultWork, hi] using
          transitionTape_eq_self (hwork i hi)

  | true =>
      simp only [if_true] at hterminal
      rw [if_pos hterminal]
      simp only [show BinaryEqPhase.scan ≠ BinaryEqPhase.done by decide,
        if_false]
      refine congrArg some (Cfg.ext rfl (transitionInput_eq_self hinput) ?_
        (transitionTape_eq_self houtput))
      funext i
      by_cases hi : i = resultIdx
      · subst i
        simp [binaryEqResultCfg, binaryEqResultWork, Γw.ofBool]
      · simpa [binaryEqResultCfg, binaryEqResultWork, hi] using
          transitionTape_eq_self (hwork i hi)

private theorem binaryEq_scan_step {n : ℕ}
    (lhsIdx rhsIdx resultIdx : Fin n)
    (inp : Tape) (work : Fin n → Tape) (out : Tape)
    (hreadEq : (work lhsIdx).read = (work rhsIdx).read)
    (hnotBlank : ¬((work lhsIdx).read = Γ.blank ∧
      (work rhsIdx).read = Γ.blank))
    (hinput : inp.read ≠ Γ.start)
    (hwork : ∀ i, (work i).read ≠ Γ.start)
    (houtput : out.read ≠ Γ.start) :
    (binaryEqTM lhsIdx rhsIdx resultIdx).step
      { state := .scan, input := inp, work := work, output := out } =
    some (binaryEqAdvanceCfg lhsIdx rhsIdx inp work out) := by
  simp only [TM.step, binaryEqTM]
  rw [if_neg hnotBlank, if_pos hreadEq]
  simp only [show BinaryEqPhase.scan ≠ BinaryEqPhase.done by decide, if_false]
  refine congrArg some (Cfg.ext rfl (transitionInput_eq_self hinput) ?_
    (transitionTape_eq_self houtput))
  funext i
  by_cases hil : i = lhsIdx
  · subst i
    simp only [binaryEqAdvanceCfg, binaryEqAdvanceWork, if_pos]
    exact writeAndMove_readBack_right (hwork lhsIdx)
  · by_cases hir : i = rhsIdx
    · subst i
      simp only [binaryEqAdvanceCfg, binaryEqAdvanceWork, if_neg hil, if_pos]
      exact writeAndMove_readBack_right (hwork rhsIdx)
    · simpa [binaryEqAdvanceCfg, binaryEqAdvanceWork, hil, hir] using
        transitionTape_eq_self (hwork i)

private theorem binaryEq_terminal_reachesIn {n : ℕ}
    (lhsIdx rhsIdx resultIdx : Fin n)
    (hdistinct : BinaryEqDistinct lhsIdx rhsIdx resultIdx)
    (lhs rhs : List Bool) (result : Bool)
    (hdecision : decide (lhs = rhs) = result)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hlhs : (work₀ lhsIdx).HasBinarySuffix lhs)
    (hrhs : (work₀ rhsIdx).HasBinarySuffix rhs)
    (hresult : (work₀ resultIdx).HasBinaryPrefix [])
    (hterminal : if result then
      (work₀ lhsIdx).read = Γ.blank ∧ (work₀ rhsIdx).read = Γ.blank
      else ¬((work₀ lhsIdx).read = (work₀ rhsIdx).read))
    (hinput : inp₀.read ≠ Γ.start)
    (hother : ∀ i, i ≠ lhsIdx → i ≠ rhsIdx → i ≠ resultIdx →
      (work₀ i).read ≠ Γ.start)
    (houtput : out₀.read ≠ Γ.start) :
    ∃ c' t,
      t ≤ binaryEqTime lhs rhs ∧
      (binaryEqTM lhsIdx rhsIdx resultIdx).reachesIn t
        { state := (binaryEqTM lhsIdx rhsIdx resultIdx).qstart
          input := inp₀
          work := work₀
          output := out₀ } c' ∧
      (binaryEqTM lhsIdx rhsIdx resultIdx).halted c' ∧
      c'.input = inp₀ ∧
      (c'.work resultIdx).HasBinaryPrefix [decide (lhs = rhs)] ∧
      (c'.work lhsIdx).cells = (work₀ lhsIdx).cells ∧
      (c'.work rhsIdx).cells = (work₀ rhsIdx).cells ∧
      1 ≤ (c'.work lhsIdx).head ∧
      1 ≤ (c'.work rhsIdx).head ∧
      (∀ i, i ≠ lhsIdx → i ≠ rhsIdx → i ≠ resultIdx →
        c'.work i = work₀ i) ∧
      c'.output = out₀ := by
  have hwork : ∀ i, i ≠ resultIdx → (work₀ i).read ≠ Γ.start := by
    intro i hir
    by_cases hil : i = lhsIdx
    · subst i
      exact hlhs.read_ne_start
    · by_cases hirhs : i = rhsIdx
      · subst i
        exact hrhs.read_ne_start
      · exact hother i hil hirhs hir
  have hstep := binaryEq_terminal_step lhsIdx rhsIdx resultIdx result
    inp₀ work₀ out₀ hterminal hinput hwork houtput
  let c' := binaryEqResultCfg resultIdx result inp₀ work₀ out₀
  refine ⟨c', 1, by simp [binaryEqTime], .step hstep .zero, rfl, rfl, ?_, ?_,
    ?_, ?_, ?_, ?_, rfl⟩
  · rw [hdecision]
    cases result with
    | false =>
        simpa [c', binaryEqResultCfg, binaryEqResultWork, Γw.ofBool] using
          Tape.hasBinaryPrefix_write_bit false hresult
    | true =>
        simpa [c', binaryEqResultCfg, binaryEqResultWork, Γw.ofBool] using
          Tape.hasBinaryPrefix_write_bit true hresult
  · change (Function.update work₀ resultIdx _ lhsIdx).cells = _
    rw [Function.update_of_ne hdistinct.lhs_result]
  · change (Function.update work₀ resultIdx _ rhsIdx).cells = _
    rw [Function.update_of_ne hdistinct.rhs_result]
  · change 1 ≤ (Function.update work₀ resultIdx _ lhsIdx).head
    rw [Function.update_of_ne hdistinct.lhs_result]
    exact hlhs.1
  · change 1 ≤ (Function.update work₀ resultIdx _ rhsIdx).head
    rw [Function.update_of_ne hdistinct.rhs_result]
    exact hrhs.1
  · intro i hil hirhs hir
    simp [c', binaryEqResultCfg, binaryEqResultWork, hir]

private theorem binaryEq_suffix_reachesIn {n : ℕ}
    (lhsIdx rhsIdx resultIdx : Fin n)
    (hdistinct : BinaryEqDistinct lhsIdx rhsIdx resultIdx)
    (lhs rhs : List Bool)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hlhs : (work₀ lhsIdx).HasBinarySuffix lhs)
    (hrhs : (work₀ rhsIdx).HasBinarySuffix rhs)
    (hresult : (work₀ resultIdx).HasBinaryPrefix [])
    (hinput : inp₀.read ≠ Γ.start)
    (hother : ∀ i, i ≠ lhsIdx → i ≠ rhsIdx → i ≠ resultIdx →
      (work₀ i).read ≠ Γ.start)
    (houtput : out₀.read ≠ Γ.start) :
    ∃ c' t,
      t ≤ binaryEqTime lhs rhs ∧
      (binaryEqTM lhsIdx rhsIdx resultIdx).reachesIn t
        { state := (binaryEqTM lhsIdx rhsIdx resultIdx).qstart
          input := inp₀
          work := work₀
          output := out₀ } c' ∧
      (binaryEqTM lhsIdx rhsIdx resultIdx).halted c' ∧
      c'.input = inp₀ ∧
      (c'.work resultIdx).HasBinaryPrefix [decide (lhs = rhs)] ∧
      (c'.work lhsIdx).cells = (work₀ lhsIdx).cells ∧
      (c'.work rhsIdx).cells = (work₀ rhsIdx).cells ∧
      1 ≤ (c'.work lhsIdx).head ∧
      1 ≤ (c'.work rhsIdx).head ∧
      (∀ i, i ≠ lhsIdx → i ≠ rhsIdx → i ≠ resultIdx →
        c'.work i = work₀ i) ∧
      c'.output = out₀ := by
  induction lhs generalizing rhs inp₀ work₀ out₀ with
  | nil =>
      cases rhs with
      | nil =>
          apply binaryEq_terminal_reachesIn lhsIdx rhsIdx resultIdx hdistinct
            [] [] true (by simp) inp₀ work₀ out₀ hlhs hrhs hresult
          · simp [hlhs.read_nil, hrhs.read_nil]
          · exact hinput
          · exact hother
          · exact houtput
      | cons rhsBit rhsTail =>
          apply binaryEq_terminal_reachesIn lhsIdx rhsIdx resultIdx hdistinct
            [] (rhsBit :: rhsTail) false (by simp) inp₀ work₀ out₀ hlhs hrhs
            hresult
          · rw [hlhs.read_nil, hrhs.read_cons]
            cases rhsBit <;> decide
          · exact hinput
          · exact hother
          · exact houtput
  | cons lhsBit lhsTail ih =>
      cases rhs with
      | nil =>
          apply binaryEq_terminal_reachesIn lhsIdx rhsIdx resultIdx hdistinct
            (lhsBit :: lhsTail) [] false (by simp) inp₀ work₀ out₀ hlhs hrhs
            hresult
          · rw [hlhs.read_cons, hrhs.read_nil]
            cases lhsBit <;> decide
          · exact hinput
          · exact hother
          · exact houtput
      | cons rhsBit rhsTail =>
          by_cases hbit : lhsBit = rhsBit
          · subst rhsBit
            have hworkRead : ∀ i, (work₀ i).read ≠ Γ.start := by
              intro i
              by_cases hil : i = lhsIdx
              · subst i
                exact hlhs.read_ne_start
              · by_cases hir : i = rhsIdx
                · subst i
                  exact hrhs.read_ne_start
                · by_cases hires : i = resultIdx
                  · subst i
                    rw [hresult.read_blank]
                    decide
                  · exact hother i hil hir hires
            have hreadEq : (work₀ lhsIdx).read = (work₀ rhsIdx).read := by
              rw [hlhs.read_cons, hrhs.read_cons]
            have hnotBlank : ¬((work₀ lhsIdx).read = Γ.blank ∧
                (work₀ rhsIdx).read = Γ.blank) := by
              intro hblank
              rw [hlhs.read_cons] at hblank
              cases lhsBit <;> simp [Γ.ofBool] at hblank
            have hstep := binaryEq_scan_step lhsIdx rhsIdx resultIdx inp₀ work₀
              out₀ hreadEq hnotBlank hinput hworkRead houtput
            let work₁ := binaryEqAdvanceWork lhsIdx rhsIdx work₀
            have hlhs₁ : (work₁ lhsIdx).HasBinarySuffix lhsTail := by
              simpa [work₁, binaryEqAdvanceWork] using hlhs.move_right_cons
            have hrhs₁ : (work₁ rhsIdx).HasBinarySuffix rhsTail := by
              simp only [work₁, binaryEqAdvanceWork,
                if_neg (Ne.symm hdistinct.lhs_rhs), if_pos]
              exact hrhs.move_right_cons
            have hresult₁ : (work₁ resultIdx).HasBinaryPrefix [] := by
              simpa [work₁, binaryEqAdvanceWork,
                Ne.symm hdistinct.lhs_result,
                Ne.symm hdistinct.rhs_result] using hresult
            have hother₁ : ∀ i, i ≠ lhsIdx → i ≠ rhsIdx → i ≠ resultIdx →
                (work₁ i).read ≠ Γ.start := by
              intro i hil hir hires
              simpa [work₁, binaryEqAdvanceWork, hil, hir] using
                hother i hil hir hires
            obtain ⟨c', t, htime, hreach, hhalt, hfinalInput, hfinalResult,
                hfinalLhs, hfinalRhs, hfinalLhsHead, hfinalRhsHead,
                hfinalOther, hfinalOutput⟩ :=
              ih rhsTail inp₀ work₁ out₀ hlhs₁ hrhs₁ hresult₁ hinput hother₁
                houtput
            have hreach' : (binaryEqTM lhsIdx rhsIdx resultIdx).reachesIn (t + 1)
                { state := (binaryEqTM lhsIdx rhsIdx resultIdx).qstart
                  input := inp₀
                  work := work₀
                  output := out₀ } c' := by
              exact .step hstep (by
                simpa [work₁, binaryEqAdvanceCfg] using hreach)
            refine ⟨c', t + 1, ?_, hreach', hhalt, hfinalInput, ?_, ?_, ?_,
              hfinalLhsHead, hfinalRhsHead, ?_, hfinalOutput⟩
            · simp only [binaryEqTime, List.length_cons] at htime ⊢
              omega
            · simpa using hfinalResult
            · simpa [work₁, binaryEqAdvanceWork, Tape.move_cells] using hfinalLhs
            · simpa [work₁, binaryEqAdvanceWork, Tape.move_cells,
                Ne.symm hdistinct.lhs_rhs] using hfinalRhs
            · intro i hil hir hires
              simpa [work₁, binaryEqAdvanceWork, hil, hir] using
                hfinalOther i hil hir hires
          · apply binaryEq_terminal_reachesIn lhsIdx rhsIdx resultIdx hdistinct
              (lhsBit :: lhsTail) (rhsBit :: rhsTail) false (by simp [hbit])
              inp₀ work₀ out₀ hlhs hrhs hresult
            · rw [hlhs.read_cons, hrhs.read_cons]
              intro heq
              cases lhsBit <;> cases rhsBit <;> simp_all [Γ.ofBool]
            · exact hinput
            · exact hother
            · exact houtput

theorem binaryEqTM_reachesIn_frame_internal {n : ℕ}
    (lhsIdx rhsIdx resultIdx : Fin n)
    (hdistinct : BinaryEqDistinct lhsIdx rhsIdx resultIdx)
    (lhs rhs : List Bool)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hlhs : (work₀ lhsIdx).HasBinaryString lhs)
    (hrhs : (work₀ rhsIdx).HasBinaryString rhs)
    (hresult : (work₀ resultIdx).HasBinaryPrefix [])
    (hinput : inp₀.read ≠ Γ.start)
    (hother : ∀ i, i ≠ lhsIdx → i ≠ rhsIdx → i ≠ resultIdx →
      (work₀ i).read ≠ Γ.start)
    (houtput : out₀.read ≠ Γ.start) :
    ∃ c' t,
      t ≤ binaryEqTime lhs rhs ∧
      (binaryEqTM lhsIdx rhsIdx resultIdx).reachesIn t
        { state := (binaryEqTM lhsIdx rhsIdx resultIdx).qstart
          input := inp₀
          work := work₀
          output := out₀ } c' ∧
      (binaryEqTM lhsIdx rhsIdx resultIdx).halted c' ∧
      c'.input = inp₀ ∧
      (c'.work resultIdx).HasBinaryPrefix [decide (lhs = rhs)] ∧
      (c'.work lhsIdx).HasBinaryContent lhs ∧
      1 ≤ (c'.work lhsIdx).head ∧
      (c'.work rhsIdx).HasBinaryContent rhs ∧
      1 ≤ (c'.work rhsIdx).head ∧
      (∀ i, i ≠ lhsIdx → i ≠ rhsIdx → i ≠ resultIdx →
        c'.work i = work₀ i) ∧
      c'.output = out₀ := by
  obtain ⟨c', t, htime, hreach, hhalt, hfinalInput, hfinalResult,
      hfinalLhs, hfinalRhs, hfinalLhsHead, hfinalRhsHead, hfinalOther,
      hfinalOutput⟩ :=
    binaryEq_suffix_reachesIn lhsIdx rhsIdx resultIdx hdistinct lhs rhs
      inp₀ work₀ out₀ hlhs.hasBinarySuffix hrhs.hasBinarySuffix hresult
      hinput hother houtput
  refine ⟨c', t, htime, hreach, hhalt, hfinalInput, hfinalResult, ?_,
    hfinalLhsHead, ?_, hfinalRhsHead, hfinalOther, hfinalOutput⟩
  · simpa only [Tape.HasBinaryContent, hfinalLhs] using hlhs.hasBinaryContent
  · simpa only [Tape.HasBinaryContent, hfinalRhs] using hrhs.hasBinaryContent

theorem binaryEqTM_hoareTime_frame_internal {n : ℕ}
    (lhsIdx rhsIdx resultIdx : Fin n)
    (hdistinct : BinaryEqDistinct lhsIdx rhsIdx resultIdx)
    (lhs rhs : List Bool)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hlhs : (work₀ lhsIdx).HasBinaryString lhs)
    (hrhs : (work₀ rhsIdx).HasBinaryString rhs)
    (hresult : (work₀ resultIdx).HasBinaryPrefix [])
    (hinput : inp₀.read ≠ Γ.start)
    (hother : ∀ i, i ≠ lhsIdx → i ≠ rhsIdx → i ≠ resultIdx →
      (work₀ i).read ≠ Γ.start)
    (houtput : out₀.read ≠ Γ.start) :
    (binaryEqTM lhsIdx rhsIdx resultIdx).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        (work resultIdx).HasBinaryPrefix [decide (lhs = rhs)] ∧
        (work lhsIdx).HasBinaryContent lhs ∧
        1 ≤ (work lhsIdx).head ∧
        (work rhsIdx).HasBinaryContent rhs ∧
        1 ≤ (work rhsIdx).head ∧
        (∀ i, i ≠ lhsIdx → i ≠ rhsIdx → i ≠ resultIdx →
          work i = work₀ i) ∧
        out = out₀)
      (binaryEqTime lhs rhs) := by
  intro inp work out hpre
  rcases hpre with ⟨hinp, hworkEq, hout⟩
  subst inp
  subst work
  subst out
  obtain ⟨c, time, htime, hreach, hhalt, hcInput, hcResult, hcLhs,
      hcLhsHead, hcRhs, hcRhsHead, hcOther, hcOutput⟩ :=
    binaryEqTM_reachesIn_frame_internal lhsIdx rhsIdx resultIdx hdistinct
      lhs rhs inp₀ work₀ out₀ hlhs hrhs hresult hinput hother houtput
  exact ⟨c, time, htime, hreach, hhalt, hcInput, hcResult, hcLhs, hcLhsHead,
    hcRhs, hcRhsHead, hcOther, hcOutput⟩

theorem binaryEqTM_hoareTimeSpace_frame_internal {n : ℕ}
    (lhsIdx rhsIdx resultIdx : Fin n)
    (hdistinct : BinaryEqDistinct lhsIdx rhsIdx resultIdx)
    (lhs rhs : List Bool) (inputLength initialSpace : ℕ)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hlhs : (work₀ lhsIdx).HasBinaryString lhs)
    (hrhs : (work₀ rhsIdx).HasBinaryString rhs)
    (hresult : (work₀ resultIdx).HasBinaryPrefix [])
    (hinput : inp₀.read ≠ Γ.start)
    (hother : ∀ i, i ≠ lhsIdx → i ≠ rhsIdx → i ≠ resultIdx →
      (work₀ i).read ≠ Γ.start)
    (houtput : out₀.read ≠ Γ.start)
    (hinitial :
      ({ state := (binaryEqTM lhsIdx rhsIdx resultIdx).qstart,
         input := inp₀,
         work := work₀,
         output := out₀ } :
        Cfg n (binaryEqTM lhsIdx rhsIdx resultIdx).Q).WithinAuxSpace
          inputLength initialSpace) :
    (binaryEqTM lhsIdx rhsIdx resultIdx).HoareTimeSpace
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        (work resultIdx).HasBinaryPrefix [decide (lhs = rhs)] ∧
        (work lhsIdx).HasBinaryContent lhs ∧
        1 ≤ (work lhsIdx).head ∧
        (work rhsIdx).HasBinaryContent rhs ∧
        1 ≤ (work rhsIdx).head ∧
        (∀ i, i ≠ lhsIdx → i ≠ rhsIdx → i ≠ resultIdx →
          work i = work₀ i) ∧
        out = out₀)
      (binaryEqTime lhs rhs) inputLength
      (initialSpace + binaryEqTime lhs rhs) := by
  apply (binaryEqTM_hoareTime_frame_internal lhsIdx rhsIdx resultIdx hdistinct
    lhs rhs inp₀ work₀ out₀ hlhs hrhs hresult hinput hother
    houtput).toHoareTimeSpace
  intro inp work out hpre
  rcases hpre with ⟨hinp, hworkEq, hout⟩
  subst inp
  subst work
  subst out
  exact hinitial

theorem binaryEqRewindTM_hoareTime_frame_internal {n : ℕ}
    (lhsIdx rhsIdx resultIdx : Fin n)
    (hdistinct : BinaryEqDistinct lhsIdx rhsIdx resultIdx)
    (lhs rhs : List Bool)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hlhs : (work₀ lhsIdx).HasBinaryString lhs)
    (hlhsStart : (work₀ lhsIdx).cells 0 = Γ.start)
    (hrhs : (work₀ rhsIdx).HasBinaryString rhs)
    (hrhsStart : (work₀ rhsIdx).cells 0 = Γ.start)
    (hresult : (work₀ resultIdx).HasBinaryPrefix [])
    (hresultStart : (work₀ resultIdx).cells 0 = Γ.start)
    (hinput : Parked inp₀)
    (hother : ∀ i, i ≠ lhsIdx → i ≠ rhsIdx → i ≠ resultIdx →
      Parked (work₀ i))
    (houtput : Parked out₀) :
    (binaryEqRewindTM lhsIdx rhsIdx resultIdx).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        work = Function.update work₀ resultIdx
          ((Tape.init ([decide (lhs = rhs)].map Γ.ofBool)).move Dir3.right) ∧
        out = out₀)
      (binaryEqRewindTime lhs rhs) := by
  let comparisonTime := binaryEqTime lhs rhs
  let resultBits := [decide (lhs = rhs)]
  let compared : TapePred n := fun inp work out =>
    inp = inp₀ ∧
    (work resultIdx).HasBinaryPrefix resultBits ∧
    (work resultIdx).cells 0 = Γ.start ∧
    (work lhsIdx).HasBinaryContent lhs ∧
    (work lhsIdx).cells 0 = Γ.start ∧
    1 ≤ (work lhsIdx).head ∧
    (work lhsIdx).head ≤ comparisonTime + 1 ∧
    (work rhsIdx).HasBinaryContent rhs ∧
    (work rhsIdx).cells 0 = Γ.start ∧
    1 ≤ (work rhsIdx).head ∧
    (work rhsIdx).head ≤ comparisonTime + 1 ∧
    (∀ i, i ≠ lhsIdx → i ≠ rhsIdx → i ≠ resultIdx →
      work i = work₀ i) ∧
    out = out₀
  have hcompare : (binaryEqTM lhsIdx rhsIdx resultIdx).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      compared comparisonTime := by
    intro inp work out hpre
    rcases hpre with ⟨hinp, hworkEq, hout⟩
    subst inp
    subst work
    subst out
    obtain ⟨c, time, htime, hreach, hhalt, hcInput, hcResult, hcLhs,
        hcLhsHead, hcRhs, hcRhsHead, hcOther, hcOutput⟩ :=
      binaryEqTM_reachesIn_frame_internal lhsIdx rhsIdx resultIdx hdistinct
        lhs rhs inp₀ work₀ out₀ hlhs hrhs hresult hinput.read_ne_start
        (fun i hil hir hires => (hother i hil hir hires).read_ne_start)
        houtput.read_ne_start
    have hheads := head_le_start_add_of_reachesIn
      (binaryEqTM lhsIdx rhsIdx resultIdx) hreach
    have hcResultStart := work_cells_zero_eq_start_of_reachesIn resultIdx
      hreach hresultStart
    have hcLhsStart := work_cells_zero_eq_start_of_reachesIn lhsIdx hreach
      hlhsStart
    have hcRhsStart := work_cells_zero_eq_start_of_reachesIn rhsIdx hreach
      hrhsStart
    refine ⟨c, time, ?_, hreach, hhalt, ?_⟩
    · simpa [comparisonTime] using htime
    refine ⟨hcInput, ?_, hcResultStart, hcLhs, hcLhsStart, hcLhsHead, ?_,
      hcRhs, hcRhsStart, hcRhsHead, ?_, hcOther, hcOutput⟩
    · simpa [resultBits] using hcResult
    · have hbound := hheads.2.2 lhsIdx
      rw [hlhs.1] at hbound
      simp only [comparisonTime]
      omega
    · have hbound := hheads.2.2 rhsIdx
      rw [hrhs.1] at hbound
      simp only [comparisonTime]
      omega
  let rewoundLhs : TapePred n := fun inp work out =>
    inp = inp₀ ∧
    work lhsIdx = (Tape.init (lhs.map Γ.ofBool)).move Dir3.right ∧
    (work resultIdx).HasBinaryPrefix resultBits ∧
    (work resultIdx).cells 0 = Γ.start ∧
    (work rhsIdx).HasBinaryContent rhs ∧
    (work rhsIdx).cells 0 = Γ.start ∧
    1 ≤ (work rhsIdx).head ∧
    (work rhsIdx).head ≤ comparisonTime + 1 ∧
    (∀ i, i ≠ lhsIdx → i ≠ rhsIdx → i ≠ resultIdx →
      work i = work₀ i) ∧
    out = out₀
  have hrewindLhs : (rewindWorkTM lhsIdx).HoareTime compared rewoundLhs
      (comparisonTime + 1 + 2) := by
    intro inp work out hpre
    rcases hpre with ⟨hinp, hres, hresStart, hlhsContent, hlhsStart',
      hlhsHead, hlhsBound, hrhsContent, hrhsStart', hrhsHead, hrhsBound,
      hother', hout⟩
    have hworkParked : ∀ i, i ≠ lhsIdx → Parked (work i) := by
      intro i hil
      by_cases hir : i = rhsIdx
      · subst i
        exact parked_of_hasBinaryContent hrhsContent hrhsHead
      by_cases hires : i = resultIdx
      · subst i
        exact parked_of_hasBinaryPrefix hres
      rw [hother' i hil hir hires]
      exact hother i hil hir hires
    have hrun := rewindBinaryWorkTM_hoareTime_frame_internal lhsIdx lhs
      (comparisonTime + 1) inp work out hlhsContent hlhsStart'
      ⟨hlhsHead, hlhsBound⟩ (hinp ▸ hinput) hworkParked (hout ▸ houtput)
    obtain ⟨c, time, htime, hreach, hhalt, hcInput, hcLhs, hcOther,
        hcOutput⟩ := hrun inp work out ⟨rfl, rfl, rfl⟩
    refine ⟨c, time, htime, hreach, hhalt, ?_⟩
    refine ⟨hcInput.trans hinp, hcLhs, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      hcOutput.trans hout⟩
    · rw [hcOther resultIdx hdistinct.lhs_result.symm]
      exact hres
    · rw [hcOther resultIdx hdistinct.lhs_result.symm]
      exact hresStart
    · rw [hcOther rhsIdx hdistinct.lhs_rhs.symm]
      exact hrhsContent
    · rw [hcOther rhsIdx hdistinct.lhs_rhs.symm]
      exact hrhsStart'
    · rw [hcOther rhsIdx hdistinct.lhs_rhs.symm]
      exact hrhsHead
    · rw [hcOther rhsIdx hdistinct.lhs_rhs.symm]
      exact hrhsBound
    · intro i hil hir hires
      exact (hcOther i hil).trans (hother' i hil hir hires)
  let rewoundRhs : TapePred n := fun inp work out =>
    inp = inp₀ ∧
    work lhsIdx = (Tape.init (lhs.map Γ.ofBool)).move Dir3.right ∧
    work rhsIdx = (Tape.init (rhs.map Γ.ofBool)).move Dir3.right ∧
    (work resultIdx).HasBinaryPrefix resultBits ∧
    (work resultIdx).cells 0 = Γ.start ∧
    (∀ i, i ≠ lhsIdx → i ≠ rhsIdx → i ≠ resultIdx →
      work i = work₀ i) ∧
    out = out₀
  have hrewindRhs : (rewindWorkTM rhsIdx).HoareTime rewoundLhs rewoundRhs
      (comparisonTime + 1 + 2) := by
    intro inp work out hpre
    rcases hpre with ⟨hinp, hlhsEq, hres, hresStart, hrhsContent,
      hrhsStart', hrhsHead, hrhsBound, hother', hout⟩
    have hworkParked : ∀ i, i ≠ rhsIdx → Parked (work i) := by
      intro i hir
      by_cases hil : i = lhsIdx
      · subst i
        rw [hlhsEq]
        exact ⟨by simp [Tape.move],
          Tape.init_ofBool_move_right_cells_ne_start lhs⟩
      by_cases hires : i = resultIdx
      · subst i
        exact parked_of_hasBinaryPrefix hres
      rw [hother' i hil hir hires]
      exact hother i hil hir hires
    have hrun := rewindBinaryWorkTM_hoareTime_frame_internal rhsIdx rhs
      (comparisonTime + 1) inp work out hrhsContent hrhsStart'
      ⟨hrhsHead, hrhsBound⟩ (hinp ▸ hinput) hworkParked (hout ▸ houtput)
    obtain ⟨c, time, htime, hreach, hhalt, hcInput, hcRhs, hcOther,
        hcOutput⟩ := hrun inp work out ⟨rfl, rfl, rfl⟩
    refine ⟨c, time, htime, hreach, hhalt, ?_⟩
    refine ⟨hcInput.trans hinp, ?_, hcRhs, ?_, ?_, ?_,
      hcOutput.trans hout⟩
    · rw [hcOther lhsIdx hdistinct.lhs_rhs]
      exact hlhsEq
    · rw [hcOther resultIdx hdistinct.rhs_result.symm]
      exact hres
    · rw [hcOther resultIdx hdistinct.rhs_result.symm]
      exact hresStart
    · intro i hil hir hires
      exact (hcOther i hir).trans (hother' i hil hir hires)
  have hrewindResult : (rewindWorkTM resultIdx).HoareTime rewoundRhs
      (fun inp work out =>
        inp = inp₀ ∧
        work = Function.update work₀ resultIdx
          ((Tape.init (resultBits.map Γ.ofBool)).move Dir3.right) ∧
        out = out₀)
      (2 + 2) := by
    intro inp work out hpre
    rcases hpre with ⟨hinp, hlhsEq, hrhsEq, hres, hresStart, hother',
      hout⟩
    have hworkParked : ∀ i, i ≠ resultIdx → Parked (work i) := by
      intro i hires
      by_cases hil : i = lhsIdx
      · subst i
        rw [hlhsEq]
        exact ⟨by simp [Tape.move],
          Tape.init_ofBool_move_right_cells_ne_start lhs⟩
      by_cases hir : i = rhsIdx
      · subst i
        rw [hrhsEq]
        exact ⟨by simp [Tape.move],
          Tape.init_ofBool_move_right_cells_ne_start rhs⟩
      rw [hother' i hil hir hires]
      exact hother i hil hir hires
    have hrun := rewindBinaryWorkTM_hoareTime_frame_internal resultIdx
      resultBits 2 inp work out (show (work resultIdx).HasBinaryContent
        resultBits from hres.2) hresStart ⟨by rw [hres.1]; omega,
        by rw [hres.1]; simp [resultBits]⟩ (hinp ▸ hinput) hworkParked
        (hout ▸ houtput)
    obtain ⟨c, time, htime, hreach, hhalt, hcInput, hcResult, hcOther,
        hcOutput⟩ := hrun inp work out ⟨rfl, rfl, rfl⟩
    refine ⟨c, time, htime, hreach, hhalt, hcInput.trans hinp, ?_,
      hcOutput.trans hout⟩
    funext i
    by_cases hires : i = resultIdx
    · subst i
      rw [Function.update_self]
      exact hcResult
    rw [Function.update_of_ne hires, hcOther i hires]
    by_cases hil : i = lhsIdx
    · subst i
      exact hlhsEq.trans
        (Tape.eq_init_move_right_of_hasBinaryString hlhs hlhsStart).symm
    by_cases hir : i = rhsIdx
    · subst i
      exact hrhsEq.trans
        (Tape.eq_init_move_right_of_hasBinaryString hrhs hrhsStart).symm
    exact hother' i hil hir hires
  have htransitionCompared : ∀ inp work out, compared inp work out →
      compared (transitionInput inp) (fun i => transitionTape (work i))
        (transitionTape out) := by
    intro inp work out hpre
    rcases hpre with ⟨hinp, hres, hresStart, hlhsContent, hlhsStart',
      hlhsHead, hlhsBound, hrhsContent, hrhsStart', hrhsHead, hrhsBound,
      hother', hout⟩
    have hreads : ∀ i, (work i).read ≠ Γ.start := by
      intro i
      by_cases hil : i = lhsIdx
      · subst i
        exact (parked_of_hasBinaryContent hlhsContent hlhsHead).read_ne_start
      by_cases hir : i = rhsIdx
      · subst i
        exact (parked_of_hasBinaryContent hrhsContent hrhsHead).read_ne_start
      by_cases hires : i = resultIdx
      · subst i
        exact (parked_of_hasBinaryPrefix hres).read_ne_start
      rw [hother' i hil hir hires]
      exact (hother i hil hir hires).read_ne_start
    obtain ⟨hi, hw, ho⟩ := phaseTransition_eq_self_of_reads_ne_start
      (hinp ▸ hinput.read_ne_start) hreads (hout ▸ houtput.read_ne_start)
    rw [hi, hw, ho]
    exact ⟨hinp, hres, hresStart, hlhsContent, hlhsStart', hlhsHead,
      hlhsBound, hrhsContent, hrhsStart', hrhsHead, hrhsBound, hother', hout⟩
  have htransitionLhs : ∀ inp work out, rewoundLhs inp work out →
      rewoundLhs (transitionInput inp) (fun i => transitionTape (work i))
        (transitionTape out) := by
    intro inp work out hpre
    rcases hpre with ⟨hinp, hlhsEq, hres, hresStart, hrhsContent,
      hrhsStart', hrhsHead, hrhsBound, hother', hout⟩
    have hreads : ∀ i, (work i).read ≠ Γ.start := by
      intro i
      by_cases hil : i = lhsIdx
      · subst i
        rw [hlhsEq]
        exact Tape.init_ofBool_move_right_read_ne_start lhs
      by_cases hir : i = rhsIdx
      · subst i
        exact (parked_of_hasBinaryContent hrhsContent hrhsHead).read_ne_start
      by_cases hires : i = resultIdx
      · subst i
        exact (parked_of_hasBinaryPrefix hres).read_ne_start
      rw [hother' i hil hir hires]
      exact (hother i hil hir hires).read_ne_start
    obtain ⟨hi, hw, ho⟩ := phaseTransition_eq_self_of_reads_ne_start
      (hinp ▸ hinput.read_ne_start) hreads (hout ▸ houtput.read_ne_start)
    rw [hi, hw, ho]
    exact ⟨hinp, hlhsEq, hres, hresStart, hrhsContent, hrhsStart',
      hrhsHead, hrhsBound, hother', hout⟩
  have htransitionRhs : ∀ inp work out, rewoundRhs inp work out →
      rewoundRhs (transitionInput inp) (fun i => transitionTape (work i))
        (transitionTape out) := by
    intro inp work out hpre
    rcases hpre with ⟨hinp, hlhsEq, hrhsEq, hres, hresStart, hother',
      hout⟩
    have hreads : ∀ i, (work i).read ≠ Γ.start := by
      intro i
      by_cases hil : i = lhsIdx
      · subst i
        rw [hlhsEq]
        exact Tape.init_ofBool_move_right_read_ne_start lhs
      by_cases hir : i = rhsIdx
      · subst i
        rw [hrhsEq]
        exact Tape.init_ofBool_move_right_read_ne_start rhs
      by_cases hires : i = resultIdx
      · subst i
        exact (parked_of_hasBinaryPrefix hres).read_ne_start
      rw [hother' i hil hir hires]
      exact (hother i hil hir hires).read_ne_start
    obtain ⟨hi, hw, ho⟩ := phaseTransition_eq_self_of_reads_ne_start
      (hinp ▸ hinput.read_ne_start) hreads (hout ▸ houtput.read_ne_start)
    rw [hi, hw, ho]
    exact ⟨hinp, hlhsEq, hrhsEq, hres, hresStart, hother', hout⟩
  have hrewinds := seqTM_hoareTime (rewindWorkTM lhsIdx)
    (seqTM (rewindWorkTM rhsIdx) (rewindWorkTM resultIdx)) hrewindLhs
    htransitionLhs
    (seqTM_hoareTime (rewindWorkTM rhsIdx) (rewindWorkTM resultIdx)
      hrewindRhs htransitionRhs hrewindResult)
  unfold binaryEqRewindTM binaryEqRewindTime
  simpa [comparisonTime, resultBits] using
    seqTM_hoareTime (binaryEqTM lhsIdx rhsIdx resultIdx)
      (seqTM (rewindWorkTM lhsIdx)
        (seqTM (rewindWorkTM rhsIdx) (rewindWorkTM resultIdx)))
      hcompare htransitionCompared hrewinds

theorem binaryEqRewindTM_hoareTimeSpace_frame_internal {n : ℕ}
    (lhsIdx rhsIdx resultIdx : Fin n)
    (hdistinct : BinaryEqDistinct lhsIdx rhsIdx resultIdx)
    (lhs rhs : List Bool) (inputLength initialSpace : ℕ)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hlhs : (work₀ lhsIdx).HasBinaryString lhs)
    (hlhsStart : (work₀ lhsIdx).cells 0 = Γ.start)
    (hrhs : (work₀ rhsIdx).HasBinaryString rhs)
    (hrhsStart : (work₀ rhsIdx).cells 0 = Γ.start)
    (hresult : (work₀ resultIdx).HasBinaryPrefix [])
    (hresultStart : (work₀ resultIdx).cells 0 = Γ.start)
    (hinput : Parked inp₀)
    (hother : ∀ i, i ≠ lhsIdx → i ≠ rhsIdx → i ≠ resultIdx →
      Parked (work₀ i))
    (houtput : Parked out₀)
    (hinitial :
      ({ state := (binaryEqRewindTM lhsIdx rhsIdx resultIdx).qstart,
         input := inp₀,
         work := work₀,
         output := out₀ } :
        Cfg n (binaryEqRewindTM lhsIdx rhsIdx resultIdx).Q).WithinAuxSpace
          inputLength initialSpace) :
    (binaryEqRewindTM lhsIdx rhsIdx resultIdx).HoareTimeSpace
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        work = Function.update work₀ resultIdx
          ((Tape.init ([decide (lhs = rhs)].map Γ.ofBool)).move Dir3.right) ∧
        out = out₀)
      (binaryEqRewindTime lhs rhs) inputLength
      (initialSpace + binaryEqRewindTime lhs rhs) := by
  apply (binaryEqRewindTM_hoareTime_frame_internal lhsIdx rhsIdx resultIdx
    hdistinct lhs rhs inp₀ work₀ out₀ hlhs hlhsStart hrhs hrhsStart hresult
    hresultStart hinput hother houtput).toHoareTimeSpace
  intro inp work out hpre
  rcases hpre with ⟨hinp, hworkEq, hout⟩
  subst inp
  subst work
  subst out
  exact hinitial

theorem binaryEqTM_isTransducer_internal {n : ℕ}
    (lhsIdx rhsIdx resultIdx : Fin n) :
    (binaryEqTM lhsIdx rhsIdx resultIdx).IsTransducer := by
  intro phase iHead wHeads oHead
  cases phase with
  | scan =>
      simp only [binaryEqTM]
      split
      · simp only
        simp only [idleDir]
        split <;> decide
      · split
        · simp only
          simp only [idleDir]
          split <;> decide
        · simp only
          simp only [idleDir]
          split <;> decide
  | done =>
      simp only [binaryEqTM, allIdle, idleDir]
      split <;> decide

theorem binaryEqRewindTM_isTransducer_internal {n : ℕ}
    (lhsIdx rhsIdx resultIdx : Fin n) :
    (binaryEqRewindTM lhsIdx rhsIdx resultIdx).IsTransducer := by
  unfold binaryEqRewindTM
  exact (binaryEqTM_isTransducer_internal lhsIdx rhsIdx resultIdx).seqTM
    ((rewindWorkTM_isTransducer_internal lhsIdx).seqTM
      ((rewindWorkTM_isTransducer_internal rhsIdx).seqTM
        (rewindWorkTM_isTransducer_internal resultIdx)))

end TM

end Complexity
