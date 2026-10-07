/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Interop.Mathlib.TM0.Defs
import Mathlib.Tactic.Ring

/-!
# Source-step simulation on binary tracks

All work heads move together. Their contents at each relative offset encode
the source tape at that offset, so each source write or move takes one CSLib step.
-/

public section

namespace Complexity.MathlibTM0
open SymbolTracks

/-- The simulator is executing the source state with the same relative tape contents. -/
structure Sim (M : BinaryMachine) {input : List Bool} (c : M.Config)
    (d : Turing.Cfg (Fintype.card M.Alphabet) Bool (Control M.State) input) : Prop where
  /-- The source and simulator controls agree. -/
  state : d.state = some (.run c.q)
  /-- Output emission has not started. -/
  output : d.output = []
  /-- Every track agrees at every offset from its head. -/
  tape : ∀ i z, d.workTapes i (d.workTapePos i + z) = encode (c.Tape.nth z) (trackEquiv M i)

lemma Sim.read {M : BinaryMachine} {input : List Bool} {c : M.Config}
    {d : Turing.Cfg (Fintype.card M.Alphabet) Bool (Control M.State) input} (h : Sim M c d) :
    decode (fun a => d.workTapeSymbols ((trackEquiv M).symm a)) = c.Tape.head := by
  have he : (fun a => d.workTapeSymbols ((trackEquiv M).symm a)) = encode c.Tape.head := by
    funext a
    simpa [Turing.Cfg.workTapeSymbols] using h.tape ((trackEquiv M).symm a) 0
  rw [he, decode_encode]

lemma move_nth {Γ : Type*} [Inhabited Γ] (dir : Turing.Dir) (t : Turing.Tape Γ) (z : ℤ) :
    (t.move dir).nth z = t.nth (z + (moveSign dir : ℤ)) := by
  cases dir <;> simp [moveSign, sub_eq_add_neg]

lemma Sim.step {M : BinaryMachine} {input : List Bool} {c c' : M.Config}
    {d : Turing.Cfg (Fintype.card M.Alphabet) Bool (Control M.State) input}
    (h : Sim M c d) (hs : Turing.TM0.step M.code c = some c') :
    Sim M c' ((machine M).step d) := by
  cases hcode : M.code c.q c.Tape.head with
  | none => simp [Turing.TM0.step, hcode] at hs
  | some out =>
      rcases out with ⟨q, stmt⟩
      simp only [Turing.TM0.step, hcode, Option.map_some, Option.some.injEq] at hs
      subst c'
      rw [Turing.MultiTapeTM.step_apply_of_state h.state]
      simp only [machine, runAction, h.read, hcode]
      cases stmt with
      | move dir =>
          refine ⟨rfl, ?_, ?_⟩
          · simpa [Turing.Action.apply] using h.output
          · intro i z
            simp only [Turing.Action.apply, move_nth]
            convert h.tape i (z + (moveSign dir : ℤ)) using 1
            congr 1
            ring
      | write a =>
          refine ⟨rfl, ?_, ?_⟩
          · simpa [Turing.Action.apply] using h.output
          · intro i z
            simp only [Turing.Action.apply, Turing.Tape.write_nth, SignType.coe_zero, add_zero]
            by_cases hz : z = 0
            · subst z
              simp
            · rw [Function.update_of_ne (by lia), ite_eq_right hz]
              exact h.tape i z

lemma Sim.run {M : BinaryMachine} {input : List Bool} {c c' : M.Config}
    {d : Turing.Cfg (Fintype.card M.Alphabet) Bool (Control M.State) input}
    (h : Sim M c d) (t : ℕ) (hs : M.run t c = some c') :
    Sim M c' ((machine M).runFrom d t) := by
  induction t generalizing c d with
  | zero =>
      have he : c = c' := Option.some.inj hs
      subst c'
      exact h
  | succ t ih =>
      cases hstep : Turing.TM0.step M.code c with
      | none => simp [BinaryMachine.run, hstep] at hs
      | some next =>
          have hn : M.run t next = some c' := by
            simpa only [BinaryMachine.run, hstep, Option.bind_some] using hs
          simpa only [Turing.MultiTapeTM.runFrom, Function.iterate_succ_apply] using
            ih (h.step hstep) hn

end Complexity.MathlibTM0
