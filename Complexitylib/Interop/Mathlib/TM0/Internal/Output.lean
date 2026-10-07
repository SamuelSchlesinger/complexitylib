/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Interop.Mathlib.TM0.Internal.Initialization

/-!
# Emitting the complete halted output

After source halting, the simulator emits one bit per step and halts at the
first blank. Together with initialization and source simulation, this costs
at most `2 * input.length + sourceTime + output.length + 4` steps.
-/

public section

namespace Complexity.MathlibTM0
open SymbolTracks

/-- The simulator is emitting from the represented tape, after previously emitted bits. -/
structure Emitting (M : BinaryMachine) {input : List Bool} (tape : Turing.Tape M.Alphabet)
    (emitted : List Bool)
    (d : Turing.Cfg (Fintype.card M.Alphabet) Bool (Control M.State) input) : Prop where
  /-- The simulator is in its output phase. -/
  state : d.state = some .emit
  /-- The output emitted so far. -/
  output : d.output = emitted
  /-- The tracks represent the remaining tape relative to their heads. -/
  tape : ∀ i z, d.workTapes i (d.workTapePos i + z) = encode (tape.nth z) (trackEquiv M i)

lemma Sim.halt {M : BinaryMachine} {input : List Bool} {c : M.Config}
    {d : Turing.Cfg (Fintype.card M.Alphabet) Bool (Control M.State) input}
    (h : Sim M c d) (hh : Turing.TM0.step M.code c = none) :
    Emitting M c.Tape [] ((machine M).step d) := by
  have hcode : M.code c.q c.Tape.head = none := by
    simpa [Turing.TM0.step] using hh
  rw [Turing.MultiTapeTM.step_apply_of_state h.state]
  simp only [machine, runAction, h.read, hcode]
  refine ⟨rfl, ?_, ?_⟩
  · simpa [idle, Turing.Action.apply] using h.output
  · intro i z
    simpa [idle, Turing.Action.apply] using h.tape i z

lemma Emitting.read {M : BinaryMachine} {input : List Bool} {tape : Turing.Tape M.Alphabet}
    {emitted : List Bool}
    {d : Turing.Cfg (Fintype.card M.Alphabet) Bool (Control M.State) input}
    (h : Emitting M tape emitted d) :
    decode (fun a => d.workTapeSymbols ((trackEquiv M).symm a)) = tape.head := by
  have he : (fun a => d.workTapeSymbols ((trackEquiv M).symm a)) = encode tape.head := by
    funext a
    simpa [Turing.Cfg.workTapeSymbols] using h.tape ((trackEquiv M).symm a) 0
  rw [he, decode_encode]

lemma Emitting.step_bit {M : BinaryMachine} {input : List Bool} {tape : Turing.Tape M.Alphabet}
    {emitted : List Bool}
    {d : Turing.Cfg (Fintype.card M.Alphabet) Bool (Control M.State) input}
    (h : Emitting M tape emitted d) {b : Bool} (hb : tape.head = M.bit b) :
    Emitting M (tape.move .right) (emitted ++ [b]) ((machine M).step d) := by
  rw [Turing.MultiTapeTM.step_apply_of_state h.state]
  simp only [machine, h.read, hb, M.readBit_bit]
  refine ⟨rfl, ?_, ?_⟩
  · simp [Turing.Action.apply, h.output]
  · intro i z
    simp only [Turing.Action.apply, Turing.Tape.move_right_nth, SignType.coe_one]
    convert h.tape i (z + 1) using 1
    congr 1
    lia

lemma Emitting.step_blank {M : BinaryMachine} {input : List Bool}
    {tape : Turing.Tape M.Alphabet} {emitted : List Bool}
    {d : Turing.Cfg (Fintype.card M.Alphabet) Bool (Control M.State) input}
    (h : Emitting M tape emitted d) (hb : tape.head = default) :
    ((machine M).step d).state = none ∧ ((machine M).step d).output = emitted := by
  rw [Turing.MultiTapeTM.step_apply_of_state h.state]
  simp [machine, h.read, hb, M.readBit_blank, idle, Turing.Action.apply, h.output]

lemma Emitting.run {M : BinaryMachine} {input : List Bool} (output : List Bool)
    {tape : Turing.Tape M.Alphabet} {emitted : List Bool}
    {d : Turing.Cfg (Fintype.card M.Alphabet) Bool (Control M.State) input}
    (h : Emitting M tape emitted d)
    (ho : ∀ j : ℕ, tape.nth j = (output.map M.bit).getI j) :
    ((machine M).runFrom d (output.length + 1)).state = none ∧
      ((machine M).runFrom d (output.length + 1)).output = emitted ++ output := by
  induction output generalizing tape emitted d with
  | nil =>
      have hb : tape.head = default := by simpa using ho 0
      simpa [Turing.MultiTapeTM.runFrom] using h.step_blank hb
  | cons b output ih =>
      have hb : tape.head = M.bit b := by simpa using ho 0
      have ht : ∀ j : ℕ, (tape.move .right).nth j = (output.map M.bit).getI j := by
        intro j
        rw [Turing.Tape.move_right_nth]
        simpa only [List.map_cons, List.getI_cons_succ, Nat.cast_add, Nat.cast_one] using
          ho (j + 1)
      have hr := ih (h.step_bit hb) ht
      simpa [Turing.MultiTapeTM.runFrom, Function.iterate_succ_apply, List.append_assoc] using hr

lemma computes_proof (M : BinaryMachine) {input output : List Bool} {time : ℕ}
    (h : M.OutputsWithin input output time) :
    (machine M).ComputesInTimeAndSpace input output
      (2 * input.length + time + output.length + 4)
      ((machine M).spaceUsed ((machine M).initCfg input)
        (2 * input.length + time + output.length + 4)) := by
  obtain ⟨t, ht, c, hr, hh, ho⟩ := h
  have hs := (init_sim M input).run t hr
  rw [← runFrom_add] at hs
  have he := hs.halt hh
  rw [← runFrom_succ] at he
  have hy := he.run output (fun j => by rw [← Turing.Tape.right₀_nth, ho]; rfl)
  rw [← runFrom_add] at hy
  have htime : 2 * input.length + 2 + t + 1 + (output.length + 1) =
      2 * input.length + t + output.length + 4 := by lia
  rw [htime] at hy
  have heq := (machine M).runFrom_eq_of_halt ((machine M).initCfg input)
    (by lia : 2 * input.length + t + output.length + 4 ≤
      2 * input.length + time + output.length + 4) hy.1
  exact ⟨by rw [heq]; exact hy.1, by rw [heq]; simpa using hy.2, rfl⟩

end Complexity.MathlibTM0
