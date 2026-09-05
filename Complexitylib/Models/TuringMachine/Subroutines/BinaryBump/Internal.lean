/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/

module
public import Complexitylib.Models.TuringMachine.Hoare.Space
public import Complexitylib.Models.TuringMachine.Subroutines.BinaryBump.Defs
public import Mathlib.Data.Nat.Size

/-!
# The zero-extending increment — proof internals

⚠️ Unreviewed by Bolton

This file proves the exact full-frame execution of `TM.binaryBumpTM`, following the proof of
`TM.binaryBumpTM` step for step: the two machines differ in one write. The carry proof is
generalized over the already-zeroed low-order prefix, and everything it states is about the bit
*string* on the tape — no number is involved, since a widening counter is not a numeral.
-/


public section

namespace Complexity

namespace BinaryBump

/-- Internal worst-case bound for the exact step count. -/
theorem steps_le_internal (bits : List Bool) :
    steps bits ≤ 2 * bits.length + 2 := by
  induction bits with
  | nil => simp [steps]
  | cons bit bits ih =>
      cases bit
      · simp [steps]
      · simp only [steps, List.length_cons]
        omega

end BinaryBump

namespace Tape

private theorem HasBinaryContent.read_cons {t : Tape} {done : ℕ}
    {bit : Bool} {rest : List Bool}
    (h : t.HasBinaryContent (List.replicate done false ++ bit :: rest))
    (hhead : t.head = done + 1) : t.read = Γ.ofBool bit := by
  rw [Tape.read, hhead]
  have hcell := h.1 done (by simp)
  simpa using hcell

private theorem HasBinaryContent.read_nil {t : Tape} {done : ℕ}
    (h : t.HasBinaryContent (List.replicate done false))
    (hhead : t.head = done + 1) : t.read = Γ.blank := by
  rw [Tape.read, hhead]
  exact h.2 done (by simp)

end Tape

namespace BinaryBump

private theorem set_true_to_false (done : ℕ) (rest : List Bool) :
    (List.replicate done false ++ true :: rest).set done false =
      List.replicate (done + 1) false ++ rest := by
  induction done with
  | zero => rfl
  | succ done ih =>
      change false :: (List.replicate done false ++ true :: rest).set done false =
        false :: false :: (List.replicate done false ++ rest)
      congr 1

private theorem set_false_to_true (done : ℕ) (rest : List Bool) :
    (List.replicate done false ++ false :: rest).set done true =
      List.replicate done false ++ true :: rest := by
  induction done with
  | zero => rfl
  | succ done ih =>
      change false :: (List.replicate done false ++ false :: rest).set done true =
        false :: (List.replicate done false ++ true :: rest)
      congr 1

end BinaryBump

namespace TM

variable {n : ℕ} {idx : Fin n}

private theorem binaryBumpTM_ne_halt {phase : BinaryBumpPhase}
    (hne : phase ≠ .done) {c : Cfg n (binaryBumpTM idx).Q}
    (hstate : c.state = phase) :
    c.state ≠ (binaryBumpTM idx).qhalt := by
  rw [hstate]
  exact hne

/-- Carry over one low-order one: write zero and advance right. -/
private theorem binaryBumpTM_step_one (c : Cfg n (binaryBumpTM idx).Q)
    (hstate : c.state = .carry) (hread : (c.work idx).read = Γ.one)
    (hinput : c.input.read ≠ Γ.start)
    (hother : ∀ i, i ≠ idx → (c.work i).read ≠ Γ.start)
    (houtput : c.output.read ≠ Γ.start) :
    (binaryBumpTM idx).step c = some
      { state := .carry
        input := c.input
        work := Function.update c.work idx
          (((c.work idx).write Γ.zero).move Dir3.right)
        output := c.output } := by
  rw [TM.step, ite_eq_right (binaryBumpTM_ne_halt (by decide) hstate)]
  simp only [binaryBumpTM, hstate, hread]
  refine congrArg some ((Cfg.mk.injEq ..).mpr ⟨rfl, ?_, ?_, ?_⟩)
  · exact transitionInput_eq_self hinput
  · funext i
    by_cases hi : i = idx
    · subst i
      simp only [↓reduceIte, Function.update_self]
      rfl
    · rw [Function.update_of_ne hi]
      simpa only [transitionTape, TM.idleDir, TM.readBackWrite, Γw.toΓ, ite_eq_right hi]
        using transitionTape_eq_self (hother i hi)
  · exact transitionTape_eq_self houtput

/-- Resolve a carry on zero: write one and turn left. -/
private theorem binaryBumpTM_step_zero (c : Cfg n (binaryBumpTM idx).Q)
    (hstate : c.state = .carry) (hread : (c.work idx).read = Γ.zero)
    (hinput : c.input.read ≠ Γ.start)
    (hother : ∀ i, i ≠ idx → (c.work i).read ≠ Γ.start)
    (houtput : c.output.read ≠ Γ.start) :
    (binaryBumpTM idx).step c = some
      { state := .rewind
        input := c.input
        work := Function.update c.work idx
          (((c.work idx).write Γ.one).move Dir3.left)
        output := c.output } := by
  rw [TM.step, ite_eq_right (binaryBumpTM_ne_halt (by decide) hstate)]
  simp only [binaryBumpTM, hstate, hread]
  refine congrArg some ((Cfg.mk.injEq ..).mpr ⟨rfl, ?_, ?_, ?_⟩)
  · exact transitionInput_eq_self hinput
  · funext i
    by_cases hi : i = idx
    · subst i
      simp only [↓reduceIte, Function.update_self]
      rfl
    · rw [Function.update_of_ne hi]
      simpa only [transitionTape, TM.idleDir, TM.readBackWrite, Γw.toΓ, ite_eq_right hi]
        using transitionTape_eq_self (hother i hi)
  · exact transitionTape_eq_self houtput

/-- Resolve overflow on the terminating blank: append a zero — widening the string — and turn
left. This is the one step in which the two increments differ. -/
private theorem binaryBumpTM_step_blank (c : Cfg n (binaryBumpTM idx).Q)
    (hstate : c.state = .carry) (hread : (c.work idx).read = Γ.blank)
    (hinput : c.input.read ≠ Γ.start)
    (hother : ∀ i, i ≠ idx → (c.work i).read ≠ Γ.start)
    (houtput : c.output.read ≠ Γ.start) :
    (binaryBumpTM idx).step c = some
      { state := .rewind
        input := c.input
        work := Function.update c.work idx
          (((c.work idx).write Γ.zero).move Dir3.left)
        output := c.output } := by
  rw [TM.step, ite_eq_right (binaryBumpTM_ne_halt (by decide) hstate)]
  simp only [binaryBumpTM, hstate, hread]
  refine congrArg some ((Cfg.mk.injEq ..).mpr ⟨rfl, ?_, ?_, ?_⟩)
  · exact transitionInput_eq_self hinput
  · funext i
    by_cases hi : i = idx
    · subst i
      simp only [↓reduceIte, Function.update_self]
      rfl
    · rw [Function.update_of_ne hi]
      simpa only [transitionTape, TM.idleDir, TM.readBackWrite, Γw.toΓ, Γ.ofBool, ite_eq_right hi]
        using transitionTape_eq_self (hother i hi)
  · exact transitionTape_eq_self houtput

/-- Rewind one ordinary target cell to the left. -/
private theorem binaryBumpTM_step_rewind (c : Cfg n (binaryBumpTM idx).Q)
    (hstate : c.state = .rewind) (hread : (c.work idx).read ≠ Γ.start)
    (hinput : c.input.read ≠ Γ.start)
    (hother : ∀ i, i ≠ idx → (c.work i).read ≠ Γ.start)
    (houtput : c.output.read ≠ Γ.start) :
    (binaryBumpTM idx).step c = some
      { state := .rewind
        input := c.input
        work := Function.update c.work idx ((c.work idx).move Dir3.left)
        output := c.output } := by
  rw [TM.step, ite_eq_right (binaryBumpTM_ne_halt (by decide) hstate)]
  simp only [binaryBumpTM, hstate, hread, ↓reduceIte]
  refine congrArg some ((Cfg.mk.injEq ..).mpr ⟨rfl, ?_, ?_, ?_⟩)
  · exact transitionInput_eq_self hinput
  · funext i
    by_cases hi : i = idx
    · subst i
      rw [ite_eq_left rfl, Function.update_self,
        writeAndMove_readBack _ hread]
    · rw [ite_eq_right hi, Function.update_of_ne hi]
      exact transitionTape_eq_self (hother i hi)
  · exact transitionTape_eq_self houtput

/-- Bounce right from the left marker and halt. -/
private theorem binaryBumpTM_step_start (c : Cfg n (binaryBumpTM idx).Q)
    (hstate : c.state = .rewind) (hread : (c.work idx).read = Γ.start)
    (hhead : (c.work idx).head = 0)
    (hinput : c.input.read ≠ Γ.start)
    (hother : ∀ i, i ≠ idx → (c.work i).read ≠ Γ.start)
    (houtput : c.output.read ≠ Γ.start) :
    (binaryBumpTM idx).step c = some
      { state := .done
        input := c.input
        work := Function.update c.work idx ((c.work idx).move Dir3.right)
        output := c.output } := by
  rw [TM.step, ite_eq_right (binaryBumpTM_ne_halt (by decide) hstate)]
  simp only [binaryBumpTM, hstate, hread, ↓reduceIte]
  refine congrArg some ((Cfg.mk.injEq ..).mpr ⟨rfl, ?_, ?_, ?_⟩)
  · exact transitionInput_eq_self hinput
  · funext i
    by_cases hi : i = idx
    · subst i
      simp only [↓reduceIte, Function.update_self]
      show (((c.work idx).write _).move Dir3.right) =
        (c.work idx).move Dir3.right
      rw [Tape.write, ite_eq_left hhead]
    · rw [ite_eq_right hi, Function.update_of_ne hi]
      exact transitionTape_eq_self (hother i hi)
  · exact transitionTape_eq_self houtput

/-! ## Exact rewind and carry runs -/

private theorem binaryBumpTM_rewind_run (bits : List Bool)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hinp : inp₀.read ≠ Γ.start)
    (hother : ∀ i, i ≠ idx → (work₀ i).read ≠ Γ.start)
    (hout : out₀.read ≠ Γ.start) :
    ∀ head (c : Cfg n (binaryBumpTM idx).Q),
      c.state = .rewind →
      c.input = inp₀ →
      (∀ i, i ≠ idx → c.work i = work₀ i) →
      (c.work idx).HasBinaryContent bits →
      (c.work idx).cells 0 = Γ.start →
      (c.work idx).head = head →
      c.output = out₀ →
      ∃ c',
        (binaryBumpTM idx).reachesIn (head + 1) c c' ∧
        (binaryBumpTM idx).halted c' ∧
        c'.input = inp₀ ∧
        (∀ i, i ≠ idx → c'.work i = work₀ i) ∧
        (c'.work idx).HasBinaryString bits ∧
        (c'.work idx).cells 0 = Γ.start ∧
        c'.output = out₀ := by
  intro head
  induction head with
  | zero =>
      intro c hstate hinput hwork hcontent hcell0 hhead houtput
      have hread : (c.work idx).read = Γ.start := by
        rw [Tape.read, hhead]
        exact hcell0
      have hstep := binaryBumpTM_step_start c hstate hread hhead
        (by rw [hinput]; exact hinp)
        (fun i hi => by rw [hwork i hi]; exact hother i hi)
        (by rw [houtput]; exact hout)
      let c₁ : Cfg n (binaryBumpTM idx).Q :=
        { state := .done
          input := c.input
          work := Function.update c.work idx ((c.work idx).move Dir3.right)
          output := c.output }
      refine ⟨c₁, .step hstep .zero, rfl, hinput, ?_, ?_, ?_, houtput⟩
      · intro i hi
        show Function.update c.work idx ((c.work idx).move Dir3.right) i = work₀ i
        rw [Function.update_of_ne hi]
        exact hwork i hi
      · show (Function.update c.work idx ((c.work idx).move Dir3.right) idx)
          |>.HasBinaryString bits
        rw [Function.update_self]
        apply Tape.HasBinaryContent.hasBinaryString
        · simpa only [Tape.HasBinaryContent, Tape.move_cells] using hcontent
        · simp [Tape.move, hhead]
      · show (Function.update c.work idx ((c.work idx).move Dir3.right) idx).cells 0 = _
        rw [Function.update_self, Tape.move_cells]
        exact hcell0
  | succ head ih =>
      intro c hstate hinput hwork hcontent hcell0 hhead houtput
      have hread : (c.work idx).read ≠ Γ.start := by
        rw [Tape.read, hhead]
        exact hcontent.cells_ne_start (head + 1) (by omega)
      have hstep := binaryBumpTM_step_rewind c hstate hread
        (by rw [hinput]; exact hinp)
        (fun i hi => by rw [hwork i hi]; exact hother i hi)
        (by rw [houtput]; exact hout)
      let c₁ : Cfg n (binaryBumpTM idx).Q :=
        { state := .rewind
          input := c.input
          work := Function.update c.work idx ((c.work idx).move Dir3.left)
          output := c.output }
      obtain ⟨c', hreach, hhalt, hinput', hwork', hstring, hcell0', houtput'⟩ :=
        ih c₁ rfl hinput
          (fun i hi => by
            show Function.update c.work idx ((c.work idx).move Dir3.left) i = work₀ i
            rw [Function.update_of_ne hi]
            exact hwork i hi)
          (by
            show (Function.update c.work idx ((c.work idx).move Dir3.left) idx)
              |>.HasBinaryContent bits
            rw [Function.update_self]
            simpa only [Tape.HasBinaryContent, Tape.move_cells] using hcontent)
          (by
            show (Function.update c.work idx ((c.work idx).move Dir3.left) idx).cells 0 = _
            rw [Function.update_self, Tape.move_cells]
            exact hcell0)
          (by
            show (Function.update c.work idx ((c.work idx).move Dir3.left) idx).head = head
            rw [Function.update_self]
            simp [Tape.move, hhead])
          houtput
      refine ⟨c', ?_, hhalt, hinput', hwork', hstring, hcell0', houtput'⟩
      simpa [Nat.succ_eq_add_one, Nat.add_assoc] using
        (TM.reachesIn.step hstep hreach)

private theorem binaryBumpTM_carry_run
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hinp : inp₀.read ≠ Γ.start)
    (hother : ∀ i, i ≠ idx → (work₀ i).read ≠ Γ.start)
    (hout : out₀.read ≠ Γ.start) :
    ∀ done bits (c : Cfg n (binaryBumpTM idx).Q),
      c.state = .carry →
      c.input = inp₀ →
      (∀ i, i ≠ idx → c.work i = work₀ i) →
      (c.work idx).HasBinaryContent (List.replicate done false ++ bits) →
      (c.work idx).cells 0 = Γ.start →
      (c.work idx).head = done + 1 →
      c.output = out₀ →
      ∃ c',
        (binaryBumpTM idx).reachesIn (done + BinaryBump.steps bits) c c' ∧
        (binaryBumpTM idx).halted c' ∧
        c'.input = inp₀ ∧
        (∀ i, i ≠ idx → c'.work i = work₀ i) ∧
        (c'.work idx).HasBinaryString
          (List.replicate done false ++ BinaryBump.bump bits) ∧
        (c'.work idx).cells 0 = Γ.start ∧
        c'.output = out₀ := by
  intro done bits
  induction bits generalizing done with
  | nil =>
      intro c hstate hinput hwork hcontent hcell0 hhead houtput
      have hcontent' : (c.work idx).HasBinaryContent (List.replicate done false) := by
        simpa using hcontent
      have hread : (c.work idx).read = Γ.blank :=
        hcontent'.read_nil hhead
      have hstep := binaryBumpTM_step_blank c hstate hread
        (by rw [hinput]; exact hinp)
        (fun i hi => by rw [hwork i hi]; exact hother i hi)
        (by rw [houtput]; exact hout)
      let target : Tape := ((c.work idx).write Γ.zero).move Dir3.left
      have htargetContent : target.HasBinaryContent
          (List.replicate done false ++ [false]) := by
        have hwrite := hcontent'.write_append false (by simpa using hhead)
        simpa only [Γ.ofBool, target, Tape.HasBinaryContent, Tape.move_cells] using hwrite
      have htargetCell0 : target.cells 0 = Γ.start := by
        exact Tape.write_move_cell0 Γ.zero Dir3.left hcell0
      have htargetHead : target.head = done := by
        simp [target, Tape.move, Tape.write_head, hhead]
      let c₁ : Cfg n (binaryBumpTM idx).Q :=
        { state := .rewind
          input := c.input
          work := Function.update c.work idx target
          output := c.output }
      obtain ⟨c', hreach, hhalt, hinput', hwork', hstring, hcell0', houtput'⟩ :=
        binaryBumpTM_rewind_run (idx := idx)
          (List.replicate done false ++ [false]) inp₀ work₀ out₀ hinp hother hout
          done c₁ rfl hinput
          (fun i hi => by
            show Function.update c.work idx target i = work₀ i
            rw [Function.update_of_ne hi]
            exact hwork i hi)
          (by
            show (Function.update c.work idx target idx).HasBinaryContent _
            rw [Function.update_self]
            exact htargetContent)
          (by
            show (Function.update c.work idx target idx).cells 0 = _
            rw [Function.update_self]
            exact htargetCell0)
          (by
            show (Function.update c.work idx target idx).head = done
            rw [Function.update_self]
            exact htargetHead)
          houtput
      refine ⟨c', ?_, hhalt, hinput', hwork', ?_, hcell0', houtput'⟩
      · simpa [BinaryBump.steps, Nat.add_assoc] using
          (TM.reachesIn.step hstep hreach)
      · simpa [BinaryBump.bump] using hstring
  | cons bit rest ih =>
      cases bit with
      | false =>
          intro c hstate hinput hwork hcontent hcell0 hhead houtput
          have hread : (c.work idx).read = Γ.zero :=
            hcontent.read_cons hhead
          have hstep := binaryBumpTM_step_zero c hstate hread
            (by rw [hinput]; exact hinp)
            (fun i hi => by rw [hwork i hi]; exact hother i hi)
            (by rw [houtput]; exact hout)
          let target : Tape := ((c.work idx).write Γ.one).move Dir3.left
          have htargetContent : target.HasBinaryContent
              (List.replicate done false ++ true :: rest) := by
            have hwrite := hcontent.write_set true hhead (by simp)
            rw [BinaryBump.set_false_to_true] at hwrite
            simpa only [Γ.ofBool, target, Tape.HasBinaryContent, Tape.move_cells] using hwrite
          have htargetCell0 : target.cells 0 = Γ.start := by
            exact Tape.write_move_cell0 Γ.one Dir3.left hcell0
          have htargetHead : target.head = done := by
            simp [target, Tape.move, Tape.write_head, hhead]
          let c₁ : Cfg n (binaryBumpTM idx).Q :=
            { state := .rewind
              input := c.input
              work := Function.update c.work idx target
              output := c.output }
          obtain ⟨c', hreach, hhalt, hinput', hwork', hstring, hcell0', houtput'⟩ :=
            binaryBumpTM_rewind_run (idx := idx)
              (List.replicate done false ++ true :: rest)
              inp₀ work₀ out₀ hinp hother hout done c₁ rfl hinput
              (fun i hi => by
                show Function.update c.work idx target i = work₀ i
                rw [Function.update_of_ne hi]
                exact hwork i hi)
              (by
                show (Function.update c.work idx target idx).HasBinaryContent _
                rw [Function.update_self]
                exact htargetContent)
              (by
                show (Function.update c.work idx target idx).cells 0 = _
                rw [Function.update_self]
                exact htargetCell0)
              (by
                show (Function.update c.work idx target idx).head = done
                rw [Function.update_self]
                exact htargetHead)
              houtput
          refine ⟨c', ?_, hhalt, hinput', hwork', ?_, hcell0', houtput'⟩
          · simpa [BinaryBump.steps, Nat.add_assoc] using
              (TM.reachesIn.step hstep hreach)
          · simpa [BinaryBump.bump] using hstring
      | true =>
          intro c hstate hinput hwork hcontent hcell0 hhead houtput
          have hread : (c.work idx).read = Γ.one :=
            hcontent.read_cons hhead
          have hstep := binaryBumpTM_step_one c hstate hread
            (by rw [hinput]; exact hinp)
            (fun i hi => by rw [hwork i hi]; exact hother i hi)
            (by rw [houtput]; exact hout)
          let target : Tape := ((c.work idx).write Γ.zero).move Dir3.right
          have htargetContent : target.HasBinaryContent
              (List.replicate (done + 1) false ++ rest) := by
            have hwrite := hcontent.write_set false hhead (by simp)
            rw [BinaryBump.set_true_to_false] at hwrite
            simpa only [Γ.ofBool, target, Tape.HasBinaryContent, Tape.move_cells] using hwrite
          have htargetCell0 : target.cells 0 = Γ.start := by
            exact Tape.write_move_cell0 Γ.zero Dir3.right hcell0
          have htargetHead : target.head = (done + 1) + 1 := by
            simp [target, Tape.move, Tape.write_head, hhead]
          let c₁ : Cfg n (binaryBumpTM idx).Q :=
            { state := .carry
              input := c.input
              work := Function.update c.work idx target
              output := c.output }
          obtain ⟨c', hreach, hhalt, hinput', hwork', hstring, hcell0', houtput'⟩ :=
            ih (done + 1) c₁ rfl hinput
              (fun i hi => by
                show Function.update c.work idx target i = work₀ i
                rw [Function.update_of_ne hi]
                exact hwork i hi)
              (by
                show (Function.update c.work idx target idx).HasBinaryContent _
                rw [Function.update_self]
                exact htargetContent)
              (by
                show (Function.update c.work idx target idx).cells 0 = _
                rw [Function.update_self]
                exact htargetCell0)
              (by
                show (Function.update c.work idx target idx).head = (done + 1) + 1
                rw [Function.update_self]
                exact htargetHead)
              houtput
          refine ⟨c', ?_, hhalt, hinput', hwork', ?_, hcell0', houtput'⟩
          · convert TM.reachesIn.step hstep hreach using 1
            all_goals simp [BinaryBump.steps, Nat.add_assoc]
            all_goals omega
          · simpa [BinaryBump.bump, List.replicate_add,
              List.append_assoc] using hstring

/-! ## Public-theorem internals -/

theorem binaryBumpTime_le_internal (bits : List Bool) :
    binaryBumpTime bits ≤ 2 * bits.length + 2 :=
  BinaryBump.steps_le_internal bits

theorem binaryBumpTM_reachesIn_frame_internal
    (idx : Fin n) (bits : List Bool)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hbits : (work₀ idx).HasBinaryString bits)
    (hcell0 : (work₀ idx).cells 0 = Γ.start)
    (hinp : inp₀.read ≠ Γ.start)
    (hother : ∀ i, i ≠ idx → (work₀ i).read ≠ Γ.start)
    (hout : out₀.read ≠ Γ.start) :
    ∃ c',
      (binaryBumpTM idx).reachesIn (binaryBumpTime bits)
        { state := (binaryBumpTM idx).qstart
          input := inp₀
          work := work₀
          output := out₀ } c' ∧
      (binaryBumpTM idx).halted c' ∧
      c'.input = inp₀ ∧
      (∀ i, i ≠ idx → c'.work i = work₀ i) ∧
      (c'.work idx).HasBinaryString (BinaryBump.bump bits) ∧
      (c'.work idx).cells 0 = Γ.start ∧
      c'.output = out₀ := by
  let c₀ : Cfg n (binaryBumpTM idx).Q :=
    { state := (binaryBumpTM idx).qstart
      input := inp₀
      work := work₀
      output := out₀ }
  obtain ⟨c', hreach, hhalt, hinput, hwork, hstring, hcell0', houtput⟩ :=
    binaryBumpTM_carry_run (idx := idx) inp₀ work₀ out₀ hinp hother hout
      0 bits c₀ (by rfl) (by rfl) (fun _ _ => rfl)
      (by simpa [c₀] using hbits.hasBinaryContent) hcell0
      (by simpa [c₀] using hbits.1) (by rfl)
  refine ⟨c', ?_, hhalt, hinput, hwork, ?_, hcell0', houtput⟩
  · simpa [c₀, binaryBumpTime] using hreach
  · simpa using hstring

theorem binaryBumpTM_hoareTime_frame_internal
    (idx : Fin n) (bits : List Bool)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hbits : (work₀ idx).HasBinaryString bits)
    (hcell0 : (work₀ idx).cells 0 = Γ.start)
    (hinp : inp₀.read ≠ Γ.start)
    (hother : ∀ i, i ≠ idx → (work₀ i).read ≠ Γ.start)
    (hout : out₀.read ≠ Γ.start) :
    (binaryBumpTM idx).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        (∀ i, i ≠ idx → work i = work₀ i) ∧
        (work idx).HasBinaryString (BinaryBump.bump bits) ∧
        (work idx).cells 0 = Γ.start ∧
        out = out₀)
      (binaryBumpTime bits) := by
  rintro inp work out ⟨hinput₀, hwork₀, houtput₀⟩
  obtain ⟨c', hreach, hhalt, hinput, hwork, hbits', hcell0', houtput⟩ :=
    binaryBumpTM_reachesIn_frame_internal idx bits inp₀ work₀ out₀
      hbits hcell0 hinp hother hout
  refine ⟨c', binaryBumpTime bits, le_rfl, ?_, hhalt,
    hinput, hwork, hbits', hcell0', houtput⟩
  simpa [hinput₀, hwork₀, houtput₀] using hreach

theorem binaryBumpTM_isTransducer_internal (idx : Fin n) :
    (binaryBumpTM idx).IsTransducer := by
  intro phase iHead wHeads oHead
  cases phase with
  | carry =>
      cases hread : wHeads idx <;>
        simp [binaryBumpTM, hread, idleDir] <;>
        split <;> decide
  | rewind =>
      simp only [binaryBumpTM]
      split <;> simp [idleDir] <;> split <;> decide
  | done =>
      simp [binaryBumpTM, allIdle, idleDir]
      split <;> decide

end TM

end Complexity
