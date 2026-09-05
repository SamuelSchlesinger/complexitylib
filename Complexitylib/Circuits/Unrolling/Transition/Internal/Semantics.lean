/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.Encoding.Formula.Batch
public import Complexitylib.Circuits.Unrolling.Transition.Defs

/-!
# Semantic correctness of one-step transition formulas

This file proves that the formulas for a bounded Turing-machine transition
evaluate to the halted-or-successor configuration selected by one choice bit.
The proofs first decode reads and complete local transition cases, then verify
the head-movement and tape-write formulas atom by atom.
-/


public section

namespace Complexity

namespace CircuitUnrolling

theorem configVar_eval_internal (tm : NTM k) (T base : ℕ)
    (atom : ConfigAtom tm T) (assignment : ℕ → Bool) (c : Cfg k tm.Q)
    (hconfig : ∀ oldAtom,
      assignment (configWire tm T base oldAtom) = oldAtom.value c) :
    (configVar tm T base atom).eval assignment = atom.value c := by
  simp only [configVar, BoolFormula.eval]
  exact hconfig atom

theorem haltVar_eval_internal (tm : NTM k) (T base : ℕ)
    (assignment : ℕ → Bool) (c : Cfg k tm.Q)
    (hconfig : ∀ atom,
      assignment (configWire tm T base atom) = atom.value c) :
    (haltVar tm T base).eval assignment = decide (c.state = tm.qhalt) := by
  rw [haltVar, configVar_eval_internal tm T base (.state tm.qhalt) assignment c hconfig]
  rfl

theorem readFormula_eval_internal (tm : NTM k) (T base : ℕ)
    (tape : TapeSlot k) (symbol : Γ) (assignment : ℕ → Bool)
    (c : Cfg k tm.Q)
    (hconfig : ∀ atom,
      assignment (configWire tm T base atom) = atom.value c)
    (hhead : (tape.get c).head < T + 1) :
    (readFormula tm T base tape symbol).eval assignment =
      decide ((tape.get c).read = symbol) := by
  rw [Bool.eq_iff_iff, decide_eq_true_eq]
  simp only [readFormula, BoolFormula.eval_disjs, List.any_eq_true]
  constructor
  · rintro ⟨formula, hformula, hvalue⟩
    rw [List.mem_ofFn'] at hformula
    obtain ⟨position, rfl⟩ := hformula
    simp only [BoolFormula.eval, configVar, hconfig, ConfigAtom.value,
      Bool.and_eq_true, decide_eq_true_eq] at hvalue
    simpa [Tape.read, headCellPosition, hvalue.1] using hvalue.2
  · intro hread
    let position : Fin (T + 1) := ⟨(tape.get c).head, hhead⟩
    refine ⟨_, (List.mem_ofFn' _ _).2 ⟨position, rfl⟩, ?_⟩
    simp only [BoolFormula.eval, configVar, hconfig, ConfigAtom.value,
      Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨rfl, ?_⟩
    simpa [position, headCellPosition, Tape.read] using hread

theorem caseFormula_eval_internal (tm : NTM k) (T base choiceWire : ℕ)
    (view : TransitionCase tm) (choice : Bool) (assignment : ℕ → Bool)
    (c : Cfg k tm.Q) (hchoice : assignment choiceWire = choice)
    (hconfig : ∀ atom,
      assignment (configWire tm T base atom) = atom.value c)
    (hheads : HeadsLt T c) :
    (caseFormula tm T base choiceWire view).eval assignment =
      decide (currentCase tm choice c = view) := by
  rw [Bool.eq_iff_iff, decide_eq_true_eq]
  constructor
  · intro hvalue
    rw [caseFormula, BoolFormula.eval_conjs, List.all_eq_true] at hvalue
    have hchoiceValue := hvalue (BoolFormula.literal choiceWire view.choice) (by simp)
    have hstateValue := hvalue (configVar tm T base (.state view.state)) (by simp)
    have hinputValue :=
      hvalue (readFormula tm T base .input view.inputRead) (by simp)
    have hworkValue (i : Fin k) :=
      hvalue (readFormula tm T base (.work i) (view.workRead i)) (by
        simp [List.mem_ofFn'])
    have houtputValue :=
      hvalue (readFormula tm T base .output view.outputRead) (by simp)
    have hchoiceEq : choice = view.choice := by
      simpa [BoolFormula.eval_literal, hchoice] using hchoiceValue
    have hstateEq : c.state = view.state := by
      rw [configVar_eval_internal tm T base (.state view.state) assignment c hconfig,
        ConfigAtom.value, decide_eq_true_eq] at hstateValue
      exact hstateValue
    have hinputEq : c.input.read = view.inputRead := by
      rw [readFormula_eval_internal tm T base .input view.inputRead assignment c
        hconfig (by have := hheads TapeSlot.input; omega),
        decide_eq_true_eq] at hinputValue
      exact hinputValue
    have hworkEq : (fun i => (c.work i).read) = view.workRead := by
      funext i
      have hi := hworkValue i
      rw [readFormula_eval_internal tm T base (.work i) (view.workRead i)
        assignment c hconfig (by have := hheads (.work i); omega),
        decide_eq_true_eq] at hi
      exact hi
    have houtputEq : c.output.read = view.outputRead := by
      rw [readFormula_eval_internal tm T base .output view.outputRead assignment c
        hconfig (by have := hheads TapeSlot.output; omega),
        decide_eq_true_eq] at houtputValue
      exact houtputValue
    apply TransitionCase.ext
    · exact hchoiceEq
    · exact hstateEq
    · exact hinputEq
    · exact hworkEq
    · exact houtputEq
  · intro hview
    subst view
    rw [caseFormula, BoolFormula.eval_conjs, List.all_eq_true]
    intro formula hformula
    rw [List.mem_append] at hformula
    rcases hformula with hbefore | houtput
    · rw [List.mem_append] at hbefore
      rcases hbefore with hprefix | hwork
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hprefix
        rcases hprefix with rfl | rfl | rfl
        · simp [BoolFormula.eval_literal, hchoice, currentCase]
        · rw [configVar_eval_internal tm T base
            (.state (currentCase tm choice c).state) assignment c hconfig]
          simp [ConfigAtom.value, currentCase]
        · rw [readFormula_eval_internal tm T base .input
            (currentCase tm choice c).inputRead assignment c hconfig
            (by have := hheads TapeSlot.input; omega)]
          simp [currentCase, TapeSlot.get]
      · rw [List.mem_ofFn'] at hwork
        obtain ⟨i, rfl⟩ := hwork
        rw [readFormula_eval_internal tm T base (.work i)
          ((currentCase tm choice c).workRead i) assignment c hconfig
          (by have := hheads (.work i); omega)]
        simp [currentCase, TapeSlot.get]
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at houtput
      subst formula
      rw [readFormula_eval_internal tm T base .output
        (currentCase tm choice c).outputRead assignment c hconfig
        (by have := hheads TapeSlot.output; omega)]
      simp [currentCase, TapeSlot.get]

theorem effectFormula_eval_internal (tm : NTM k) (T base choiceWire : ℕ)
    (selects : TransitionEffect tm → Bool) (choice : Bool)
    (assignment : ℕ → Bool) (c : Cfg k tm.Q)
    (hchoice : assignment choiceWire = choice)
    (hconfig : ∀ atom,
      assignment (configWire tm T base atom) = atom.value c)
    (hheads : HeadsLt T c) :
    (effectFormula tm T base choiceWire selects).eval assignment =
      selects (currentCase tm choice c).effect := by
  rw [Bool.eq_iff_iff]
  simp only [effectFormula, BoolFormula.eval_disjs, List.any_eq_true]
  constructor
  · rintro ⟨formula, hformula, hvalue⟩
    rw [List.mem_map] at hformula
    obtain ⟨view, _, rfl⟩ := hformula
    by_cases hselects : selects view.effect = true
    · rw [ite_eq_left hselects] at hvalue
      rw [caseFormula_eval_internal tm T base choiceWire view choice assignment c
        hchoice hconfig hheads, decide_eq_true_eq] at hvalue
      subst view
      exact hselects
    · rw [ite_eq_right hselects] at hvalue
      simp [BoolFormula.eval] at hvalue
  · intro hselects
    refine ⟨caseFormula tm T base choiceWire (currentCase tm choice c), ?_, ?_⟩
    · rw [List.mem_map]
      refine ⟨currentCase tm choice c, ?_, ?_⟩
      · simp [transitionCases]
      · simp [hselects]
    · rw [caseFormula_eval_internal tm T base choiceWire
        (currentCase tm choice c) choice assignment c hchoice hconfig hheads]
      simp

theorem selectedStateFormula_eval_internal
    (tm : NTM k) (T base choiceWire : ℕ) (state : tm.Q) (choice : Bool)
    (assignment : ℕ → Bool) (c : Cfg k tm.Q)
    (hchoice : assignment choiceWire = choice)
    (hconfig : ∀ atom,
      assignment (configWire tm T base atom) = atom.value c)
    (hheads : HeadsLt T c) :
    (selectedStateFormula tm T base choiceWire state).eval assignment =
      decide ((currentCase tm choice c).effect.nextState = state) := by
  simpa [selectedStateFormula] using
    effectFormula_eval_internal tm T base choiceWire
      (fun effect => decide (effect.nextState = state)) choice assignment c
      hchoice hconfig hheads

theorem selectedMoveFormula_eval_internal
    (tm : NTM k) (T base choiceWire : ℕ) (tape : TapeSlot k)
    (direction : Dir3) (choice : Bool) (assignment : ℕ → Bool)
    (c : Cfg k tm.Q) (hchoice : assignment choiceWire = choice)
    (hconfig : ∀ atom,
      assignment (configWire tm T base atom) = atom.value c)
    (hheads : HeadsLt T c) :
    (selectedMoveFormula tm T base choiceWire tape direction).eval assignment =
      decide ((currentCase tm choice c).effect.move tape = direction) := by
  simpa [selectedMoveFormula] using
    effectFormula_eval_internal tm T base choiceWire
      (fun effect => decide (effect.move tape = direction)) choice assignment c
      hchoice hconfig hheads

theorem selectedWriteFormula_eval_internal
    (tm : NTM k) (T base choiceWire : ℕ) (tape : WritableSlot k)
    (symbol : Γ) (choice : Bool) (assignment : ℕ → Bool)
    (c : Cfg k tm.Q) (hchoice : assignment choiceWire = choice)
    (hconfig : ∀ atom,
      assignment (configWire tm T base atom) = atom.value c)
    (hheads : HeadsLt T c) :
    (selectedWriteFormula tm T base choiceWire tape symbol).eval assignment =
      decide (((currentCase tm choice c).effect.write tape).toΓ = symbol) := by
  simpa [selectedWriteFormula] using
    effectFormula_eval_internal tm T base choiceWire
      (fun effect => decide ((effect.write tape).toΓ = symbol))
      choice assignment c hchoice hconfig hheads

theorem predecessorHeadFormula_eval_internal
    (tm : NTM k) (T base : ℕ) (tape : TapeSlot k)
    (target : Fin (T + 1)) (direction : Dir3) (assignment : ℕ → Bool)
    (c : Cfg k tm.Q)
    (hconfig : ∀ atom,
      assignment (configWire tm T base atom) = atom.value c)
    (hhead : (tape.get c).head < T + 1) :
    (predecessorHeadFormula tm T base tape target direction).eval assignment =
      decide (movedHeadPosition (tape.get c).head direction = target.val) := by
  rw [Bool.eq_iff_iff, decide_eq_true_eq]
  simp only [predecessorHeadFormula, BoolFormula.eval_disjs, List.any_eq_true]
  constructor
  · rintro ⟨formula, hformula, hvalue⟩
    rw [List.mem_ofFn'] at hformula
    obtain ⟨source, rfl⟩ := hformula
    dsimp only at hvalue
    by_cases hmove : movedHeadPosition source.val direction = target.val
    · rw [ite_eq_left hmove,
        configVar_eval_internal tm T base (.head tape source) assignment c hconfig,
        ConfigAtom.value, decide_eq_true_eq] at hvalue
      simpa [hvalue] using hmove
    · rw [ite_eq_right hmove] at hvalue
      simp [BoolFormula.eval] at hvalue
  · intro hmove
    let source : Fin (T + 1) := ⟨(tape.get c).head, hhead⟩
    have hsourceMove : movedHeadPosition source.val direction = target.val := by
      simpa [source] using hmove
    refine ⟨_, (List.mem_ofFn' _ _).2 ⟨source, rfl⟩, ?_⟩
    dsimp only
    rw [ite_eq_left hsourceMove,
      configVar_eval_internal tm T base (.head tape source) assignment c hconfig]
    simp [ConfigAtom.value, source]

theorem movedHeadFormula_eval_internal
    (tm : NTM k) (T base choiceWire : ℕ) (tape : TapeSlot k)
    (target : Fin (T + 1)) (choice : Bool) (assignment : ℕ → Bool)
    (c : Cfg k tm.Q) (hchoice : assignment choiceWire = choice)
    (hconfig : ∀ atom,
      assignment (configWire tm T base atom) = atom.value c)
    (hheads : HeadsLt T c) :
    (movedHeadFormula tm T base choiceWire tape target).eval assignment =
      decide (movedHeadPosition (tape.get c).head
        ((currentCase tm choice c).effect.move tape) = target.val) := by
  have hselected (direction : Dir3) :=
    selectedMoveFormula_eval_internal tm T base choiceWire tape direction
      choice assignment c hchoice hconfig hheads
  have hpredecessor (direction : Dir3) :=
    predecessorHeadFormula_eval_internal tm T base tape target direction
      assignment c hconfig (by have := hheads tape; omega)
  generalize hdirection : (currentCase tm choice c).effect.move tape = direction
  cases direction <;>
    simp [movedHeadFormula, BoolFormula.eval_disjs, BoolFormula.eval,
      hselected, hpredecessor, hdirection, movedHeadPosition]

theorem headAtCellFormula_eval_internal
    (tm : NTM k) (T base : ℕ) (tape : TapeSlot k)
    (position : Fin (T + 2)) (assignment : ℕ → Bool)
    (c : Cfg k tm.Q)
    (hconfig : ∀ atom,
      assignment (configWire tm T base atom) = atom.value c)
    (hheads : HeadsLt T c) :
    (headAtCellFormula tm T base tape position).eval assignment =
      decide ((tape.get c).head = position.val) := by
  by_cases hposition : position.val < T + 1
  · rw [headAtCellFormula, dite_eq_left hposition,
      configVar_eval_internal tm T base (.head tape ⟨position.val, hposition⟩)
        assignment c hconfig]
    rfl
  · have hne : (tape.get c).head ≠ position.val := by
      have hhead := hheads tape
      omega
    rw [headAtCellFormula, dite_eq_right hposition]
    simp [BoolFormula.eval, hne]

theorem writtenCellFormula_eval_internal
    (tm : NTM k) (T base choiceWire : ℕ) (tape : WritableSlot k)
    (position : Fin (T + 2)) (symbol : Γ) (choice : Bool)
    (assignment : ℕ → Bool) (c : Cfg k tm.Q)
    (hchoice : assignment choiceWire = choice)
    (hconfig : ∀ atom,
      assignment (configWire tm T base atom) = atom.value c)
    (hheads : HeadsLt T c) :
    (writtenCellFormula tm T base choiceWire tape position symbol).eval assignment =
      if (tape.toTapeSlot.get c).head = position.val then
        decide (((currentCase tm choice c).effect.write tape).toΓ = symbol)
      else
        decide ((tape.toTapeSlot.get c).cells position.val = symbol) := by
  simp only [writtenCellFormula, BoolFormula.eval]
  rw [headAtCellFormula_eval_internal tm T base tape.toTapeSlot position
      assignment c hconfig hheads,
    selectedWriteFormula_eval_internal tm T base choiceWire tape symbol
      choice assignment c hchoice hconfig hheads,
    configVar_eval_internal tm T base
      (.cell tape.toTapeSlot position symbol) assignment c hconfig]
  simp only [ConfigAtom.value]
  by_cases hhead : (tape.toTapeSlot.get c).head = position.val <;> simp [hhead]

theorem haltedOrFormula_eval_internal
    (tm : NTM k) (T base : ℕ) (oldValue nextValue : BoolFormula)
    (assignment : ℕ → Bool) (c : Cfg k tm.Q)
    (hconfig : ∀ atom,
      assignment (configWire tm T base atom) = atom.value c) :
    (haltedOrFormula tm T base oldValue nextValue).eval assignment =
      if c.state = tm.qhalt then oldValue.eval assignment
      else nextValue.eval assignment := by
  simp only [haltedOrFormula, BoolFormula.eval]
  rw [haltVar_eval_internal tm T base assignment c hconfig]
  by_cases hhalt : c.state = tm.qhalt <;> simp [hhalt]

private def successorConfig (tm : NTM k) (choice : Bool)
    (c : Cfg k tm.Q) : Cfg k tm.Q :=
  let effect := (currentCase tm choice c).effect
  { state := effect.nextState
    input := c.input.move (effect.move .input)
    work := fun i =>
      (c.work i).writeAndMove (effect.write (.work i)).toΓ (effect.move (.work i))
    output :=
      c.output.writeAndMove (effect.write .output).toΓ (effect.move .output) }

private theorem choiceStep_eq_self_internal (tm : NTM k) (choice : Bool)
    (c : Cfg k tm.Q) (hhalt : c.state = tm.qhalt) :
    choiceStep tm choice c = c := by
  simp [choiceStep, NTM.trace, hhalt]

private theorem choiceStep_eq_successorConfig_internal
    (tm : NTM k) (choice : Bool) (c : Cfg k tm.Q)
    (hhalt : c.state ≠ tm.qhalt) :
    choiceStep tm choice c = successorConfig tm choice c := by
  simp [choiceStep, NTM.trace, hhalt, successorConfig, currentCase,
    TransitionCase.effect, TransitionEffect.write, TransitionEffect.move]

private theorem move_head_eq_movedHeadPosition_internal (tape : Tape)
    (direction : Dir3) :
    (tape.move direction).head = movedHeadPosition tape.head direction := by
  cases direction <;> rfl

private theorem writeAndMove_head_eq_movedHeadPosition_internal (tape : Tape)
    (symbol : Γ) (direction : Dir3) :
    (tape.writeAndMove symbol direction).head =
      movedHeadPosition tape.head direction := by
  rw [Tape.writeAndMove, move_head_eq_movedHeadPosition_internal, Tape.write_head]

private theorem successorConfig_head_internal (tm : NTM k) (choice : Bool)
    (c : Cfg k tm.Q) (tape : TapeSlot k) :
    (tape.get (successorConfig tm choice c)).head =
      movedHeadPosition (tape.get c).head
        ((currentCase tm choice c).effect.move tape) := by
  cases tape with
  | input =>
      exact move_head_eq_movedHeadPosition_internal _ _
  | work i =>
      exact writeAndMove_head_eq_movedHeadPosition_internal _ _ _
  | output =>
      exact writeAndMove_head_eq_movedHeadPosition_internal _ _ _

private theorem successorConfig_input_cells_internal (tm : NTM k)
    (choice : Bool) (c : Cfg k tm.Q) (position : ℕ) :
    ((TapeSlot.input.get (successorConfig tm choice c)).cells position) =
      c.input.cells position := by
  exact congrFun (Tape.move_cells _ _) position

private theorem successorConfig_writable_cells_internal (tm : NTM k)
    (choice : Bool) (c : Cfg k tm.Q) (tape : WritableSlot k)
    (position : ℕ) :
    (tape.toTapeSlot.get (successorConfig tm choice c)).cells position =
      ((tape.toTapeSlot.get c).write
        ((currentCase tm choice c).effect.write tape).toΓ).cells position := by
  cases tape with
  | work i =>
      exact congrFun (Tape.move_cells _ _) position
  | output =>
      exact congrFun (Tape.move_cells _ _) position

private theorem write_cells_zero_internal (tape : Tape) (symbol : Γ) :
    (tape.write symbol).cells 0 = tape.cells 0 := by
  by_cases hhead : tape.head = 0
  · simp [Tape.write, hhead]
  · simp [Tape.write, hhead, Ne.symm hhead]

private theorem write_cells_of_ne_zero_internal (tape : Tape) (symbol : Γ)
    (position : ℕ) (hposition : position ≠ 0) :
    (tape.write symbol).cells position =
      if tape.head = position then symbol else tape.cells position := by
  by_cases hhead : tape.head = 0
  · simp [Tape.write, hhead, Ne.symm hposition]
  · by_cases hat : tape.head = position
    · subst position
      simp [Tape.write, hhead]
    · simp [Tape.write, hhead, hat, Ne.symm hat]

private theorem writtenCellFormula_eval_successor_internal
    (tm : NTM k) (T base choiceWire : ℕ) (tape : WritableSlot k)
    (position : Fin (T + 2)) (symbol : Γ) (choice : Bool)
    (assignment : ℕ → Bool) (c : Cfg k tm.Q)
    (hchoice : assignment choiceWire = choice)
    (hconfig : ∀ atom,
      assignment (configWire tm T base atom) = atom.value c)
    (hheads : HeadsLt T c) (hposition : position.val ≠ 0) :
    (writtenCellFormula tm T base choiceWire tape position symbol).eval assignment =
      ConfigAtom.value (successorConfig tm choice c)
        (.cell tape.toTapeSlot position symbol) := by
  rw [writtenCellFormula_eval_internal tm T base choiceWire tape position symbol
      choice assignment c hchoice hconfig hheads,
    ConfigAtom.value,
    successorConfig_writable_cells_internal tm choice c tape position.val,
    write_cells_of_ne_zero_internal _ _ position.val hposition]
  by_cases hhead : (tape.toTapeSlot.get c).head = position.val
  · simp [hhead]; rfl
  · simp [hhead]

private theorem nextFormula_eval_of_halted_internal
    (tm : NTM k) (T base choiceWire : ℕ) (atom : ConfigAtom tm T)
    (assignment : ℕ → Bool) (c : Cfg k tm.Q)
    (hconfig : ∀ oldAtom,
      assignment (configWire tm T base oldAtom) = oldAtom.value c)
    (hhalt : c.state = tm.qhalt) :
    (nextFormula tm T base choiceWire atom).eval assignment = atom.value c := by
  cases atom with
  | state state =>
      rw [nextFormula,
        haltedOrFormula_eval_internal tm T base _ _ assignment c hconfig,
        ite_eq_left hhalt,
        configVar_eval_internal tm T base (.state state) assignment c hconfig]
  | head tape position =>
      rw [nextFormula,
        haltedOrFormula_eval_internal tm T base _ _ assignment c hconfig,
        ite_eq_left hhalt,
        configVar_eval_internal tm T base (.head tape position) assignment c hconfig]
  | cell tape position symbol =>
      cases tape with
      | input =>
          exact configVar_eval_internal tm T base (.cell .input position symbol)
            assignment c hconfig
      | work i =>
          by_cases hposition : position.val = 0
          · rw [nextFormula, ite_eq_left hposition,
              configVar_eval_internal tm T base
                (.cell (.work i) position symbol) assignment c hconfig]
          · rw [nextFormula, ite_eq_right hposition,
              haltedOrFormula_eval_internal tm T base _ _ assignment c hconfig,
              ite_eq_left hhalt,
              configVar_eval_internal tm T base
                (.cell (.work i) position symbol) assignment c hconfig]
      | output =>
          by_cases hposition : position.val = 0
          · rw [nextFormula, ite_eq_left hposition,
              configVar_eval_internal tm T base
                (.cell .output position symbol) assignment c hconfig]
          · rw [nextFormula, ite_eq_right hposition,
              haltedOrFormula_eval_internal tm T base _ _ assignment c hconfig,
              ite_eq_left hhalt,
              configVar_eval_internal tm T base
                (.cell .output position symbol) assignment c hconfig]

private theorem nextFormula_eval_of_not_halted_internal
    (tm : NTM k) (T base choiceWire : ℕ) (atom : ConfigAtom tm T)
    (choice : Bool) (assignment : ℕ → Bool) (c : Cfg k tm.Q)
    (hchoice : assignment choiceWire = choice)
    (hconfig : ∀ oldAtom,
      assignment (configWire tm T base oldAtom) = oldAtom.value c)
    (hheads : HeadsLt T c) (hhalt : c.state ≠ tm.qhalt) :
    (nextFormula tm T base choiceWire atom).eval assignment =
      atom.value (successorConfig tm choice c) := by
  cases atom with
  | state state =>
      rw [nextFormula,
        haltedOrFormula_eval_internal tm T base _ _ assignment c hconfig,
        ite_eq_right hhalt,
        selectedStateFormula_eval_internal tm T base choiceWire state
          choice assignment c hchoice hconfig hheads]
      rfl
  | head tape position =>
      rw [nextFormula,
        haltedOrFormula_eval_internal tm T base _ _ assignment c hconfig,
        ite_eq_right hhalt,
        movedHeadFormula_eval_internal tm T base choiceWire tape position
          choice assignment c hchoice hconfig hheads,
        ConfigAtom.value,
        successorConfig_head_internal tm choice c tape]
  | cell tape position symbol =>
      cases tape with
      | input =>
          rw [nextFormula,
            configVar_eval_internal tm T base (.cell .input position symbol)
              assignment c hconfig]
          simp only [ConfigAtom.value, TapeSlot.get]
          have hcells := successorConfig_input_cells_internal tm choice c position.val
          simp only [TapeSlot.get] at hcells
          erw [Bool.eq_iff_iff, decide_eq_true_eq, decide_eq_true_eq]
          simp [hcells]
      | work i =>
          by_cases hposition : position.val = 0
          · rw [nextFormula, ite_eq_left hposition,
              configVar_eval_internal tm T base
                (.cell (.work i) position symbol) assignment c hconfig]
            simp only [ConfigAtom.value, TapeSlot.get]
            have hcells := successorConfig_writable_cells_internal tm choice c
              (.work i) position.val
            simp only [WritableSlot.toTapeSlot, TapeSlot.get] at hcells
            rw [hposition, write_cells_zero_internal] at hcells
            erw [Bool.eq_iff_iff, decide_eq_true_eq, decide_eq_true_eq]
            simp [hposition, hcells]
          · rw [nextFormula, ite_eq_right hposition,
              haltedOrFormula_eval_internal tm T base _ _ assignment c hconfig,
              ite_eq_right hhalt]
            simpa [WritableSlot.toTapeSlot] using
              writtenCellFormula_eval_successor_internal tm T base choiceWire
                (.work i) position symbol choice assignment c hchoice hconfig hheads hposition
      | output =>
          by_cases hposition : position.val = 0
          · rw [nextFormula, ite_eq_left hposition,
              configVar_eval_internal tm T base
                (.cell .output position symbol) assignment c hconfig]
            simp only [ConfigAtom.value, TapeSlot.get]
            have hcells := successorConfig_writable_cells_internal tm choice c
              .output position.val
            simp only [WritableSlot.toTapeSlot, TapeSlot.get] at hcells
            rw [hposition, write_cells_zero_internal] at hcells
            erw [Bool.eq_iff_iff, decide_eq_true_eq, decide_eq_true_eq]
            simp [hposition, hcells]
          · rw [nextFormula, ite_eq_right hposition,
              haltedOrFormula_eval_internal tm T base _ _ assignment c hconfig,
              ite_eq_right hhalt]
            simpa [WritableSlot.toTapeSlot] using
              writtenCellFormula_eval_successor_internal tm T base choiceWire
                .output position symbol choice assignment c hchoice hconfig hheads hposition

theorem nextFormula_eval_internal
    (tm : NTM k) (T base choiceWire : ℕ) (atom : ConfigAtom tm T)
    (choice : Bool) (assignment : ℕ → Bool) (c : Cfg k tm.Q)
    (hchoice : assignment choiceWire = choice)
    (hconfig : ∀ oldAtom,
      assignment (configWire tm T base oldAtom) = oldAtom.value c)
    (hheads : HeadsLt T c) :
    (nextFormula tm T base choiceWire atom).eval assignment =
      atom.value (choiceStep tm choice c) := by
  by_cases hhalt : c.state = tm.qhalt
  · rw [nextFormula_eval_of_halted_internal tm T base choiceWire atom
      assignment c hconfig hhalt,
      choiceStep_eq_self_internal tm choice c hhalt]
  · rw [nextFormula_eval_of_not_halted_internal tm T base choiceWire atom
      choice assignment c hchoice hconfig hheads hhalt,
      choiceStep_eq_successorConfig_internal tm choice c hhalt]

end CircuitUnrolling

end Complexity
